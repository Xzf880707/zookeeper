/**
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.zookeeper.server.persistence;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.EOFException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FilterInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.zip.Adler32;
import java.util.zip.Checksum;

import org.apache.jute.BinaryInputArchive;
import org.apache.jute.BinaryOutputArchive;
import org.apache.jute.InputArchive;
import org.apache.jute.OutputArchive;
import org.apache.jute.Record;
import org.apache.zookeeper.server.util.SerializeUtils;
import org.apache.zookeeper.txn.TxnHeader;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class implements the TxnLog interface. It provides api's
 * to access the txnlogs and add entries to it.
 * <p>
 * The format of a Transactional log is as follows:
 * <blockquote><pre>
 * LogFile:
 *     FileHeader TxnList ZeroPad
 *
 * FileHeader: {
 *     magic 4bytes (ZKLG)
 *     version 4bytes
 *     dbid 8bytes
 *   }
 *
 * TxnList:
 *     Txn || Txn TxnList
 *
 * Txn:
 *     checksum Txnlen TxnHeader Record 0x42
 *
 * checksum: 8bytes Adler32 is currently used
 *   calculated across payload -- Txnlen, TxnHeader, Record and 0x42
 *
 * Txnlen:
 *     len 4bytes
 *
 * TxnHeader: {
 *     sessionid 8bytes
 *     cxid 4bytes
 *     zxid 8bytes
 *     time 8bytes
 *     type 4bytes
 *   }
 *
 * Record:
 *     See Jute definition file for details on the various record types
 *
 * ZeroPad:
 *     0 padded to EOF (filled during preallocation stage)
 * </pre></blockquote>
 */
public class FileTxnLog implements TxnLog {
    private static final Logger LOG;
    //预分配64m大小
    static long preAllocSize =  65536 * 1024;
    //直接内存
    private static final ByteBuffer fill = ByteBuffer.allocateDirect(1);
    //魔数，用于校验日志文件的正确性，默认为1514884167
    public final static int TXNLOG_MAGIC =ByteBuffer.wrap("ZKLG".getBytes()).getInt();

    public final static int VERSION = 2;
    //日志文件名好的前缀
    public static final String LOG_FILE_PREFIX = "log";

    /** Maximum time we allow for elapsed fsync before WARNing */
    private final static long fsyncWarningThresholdMS;

    static {
        LOG = LoggerFactory.getLogger(FileTxnLog.class);
        //获得系统参数，判断系统参数配置了预分配内存大小
        String size = System.getProperty("zookeeper.preAllocSize");
        if (size != null) {
            try {
                preAllocSize = Long.parseLong(size) * 1024;
            } catch (NumberFormatException e) {
                LOG.warn(size + " is not a valid value for preAllocSize");
            }
        }
        /** Local variable to read fsync.warningthresholdms into */
        Long fsyncWarningThreshold;
        if ((fsyncWarningThreshold = Long.getLong("zookeeper.fsync.warningthresholdms")) == null)
            fsyncWarningThreshold = Long.getLong("fsync.warningthresholdms", 1000);
        fsyncWarningThresholdMS = fsyncWarningThreshold;
    }
    // 最大(也就是最新)的zxid
    long lastZxidSeen;
    volatile BufferedOutputStream logStream = null;
    volatile OutputArchive oa;
    volatile FileOutputStream fos = null;
    //log目录文件
    File logDir;
    //是否强制同步，默认是yes
    private final boolean forceSync = !System.getProperty("zookeeper.forceSync", "yes").equals("no");
    long dbId;
    private LinkedList<FileOutputStream> streamsToFlush =
        new LinkedList<FileOutputStream>();
    // 当前配置的大小
    long currentSize;
    // 写日志文件
    File logFileWrite = null;

    private volatile long syncElapsedMS = -1L;

    /**
     * constructor for FileTxnLog. Take the directory
     * where the txnlogs are stored
     * @param logDir the directory where the txnlogs are stored
     */
    public FileTxnLog(File logDir) {
        this.logDir = logDir;
    }

    /**
     * method to allow setting preallocate size
     * of log file to pad the file.
     * @param size the size to set to in bytes
     */
    public static void setPreallocSize(long size) {
        preAllocSize = size;
    }

    /**
     * creates a checksum algorithm to be used
     * @return the checksum used for this txnlog
     */
    protected Checksum makeChecksumAlgorithm(){
        return new Adler32();
    }


    /**
     * rollover the current log file to a new one.
     * @throws IOException
     */
    public synchronized void rollLog() throws IOException {
        if (logStream != null) {
            this.logStream.flush();
            this.logStream = null;
            oa = null;
        }
    }

    /**
     * close all the open file handles
     * @throws IOException
      */
    public synchronized void close() throws IOException {
        if (logStream != null) {
            logStream.close();
        }
        for (FileOutputStream log : streamsToFlush) {
            log.close();
        }
    }

    /**
     * append an entry to the transaction log
     * @param hdr the header of the transaction
     * @param txn the transaction part of the entry
     * returns true iff something appended, otw false
     */
    /****
     *
     * @param hdr 事务的头信息
     * @param txn 事务本身
     * @return
     * @throws IOException
     */
    public synchronized boolean append(TxnHeader hdr, Record txn)
        throws IOException
    {
        if (hdr == null) {
            return false;
        }
        //如果待写入的事务的事务id小于本地保存的最新的事务id，给提醒
        if (hdr.getZxid() <= lastZxidSeen) {
            LOG.warn("Current zxid " + hdr.getZxid()
                    + " is <= " + lastZxidSeen + " for "
                    + hdr.getType());
        } else {
            lastZxidSeen = hdr.getZxid();
        }
        if (logStream==null) {//新建该FileTxnLog文件的时候会走这个
           if(LOG.isInfoEnabled()){
                LOG.info("Creating new log file: " + Util.makeLogName(hdr.getZxid()));
           }
           //根据待写入的事务id创建一个新的日志文件，文件名包含事务id
           logFileWrite = new File(logDir, Util.makeLogName(hdr.getZxid()));
           fos = new FileOutputStream(logFileWrite);
           logStream=new BufferedOutputStream(fos);
           oa = BinaryOutputArchive.getArchive(logStream);
           //根据魔数、版本号和数据库id生成日志文件头,dbId默认是0
           FileHeader fhdr = new FileHeader(TXNLOG_MAGIC,VERSION, dbId);
           fhdr.serialize(oa, "fileheader");
           // Make sure that the magic number is written before padding.
           logStream.flush();
           currentSize = fos.getChannel().position();
           streamsToFlush.add(fos);
        }
        //重新计算文件大小，保证文件的大小是预分配大小的整数倍
        //可以让文件尽可能的占用连续的磁盘扇区，减少后续写入和读取文件时的磁盘寻道开销；
        //迅速占用磁盘空间，防止使用过程中所需空间不足
        currentSize = padFile(fos.getChannel());
        //序列化TxnHeader Record记录到byte[]
        byte[] buf = Util.marshallTxnEntry(hdr, txn);
        if (buf == null || buf.length == 0) {
            throw new IOException("Faulty serialization for header " +
                    "and txn");
        }
        //根据指定数组更新校验值
        Checksum crc = makeChecksumAlgorithm();
        crc.update(buf, 0, buf.length);
        oa.writeLong(crc.getValue(), "txnEntryCRC");
        //将TxnHeader Record数据写入到输出流
        //1.先计算buf数据长度写入
        //2.写入buf数组数据
        // 3.记录尾部以’B’字符结尾，写入0x42
        Util.writeTxnBytes(oa, buf);

        return true;
    }

    /**
     * pad the current file to increase its size to the next multiple of preAllocSize greater than the current size and position
     * @param fileChannel the fileChannel of the file to be padded
     * @throws IOException
     */
    /***
     *
     * @param fileChannel
     * @return
     * @throws IOException
     */
    private long padFile(FileChannel fileChannel) throws IOException {
        //计算新的文件大小，并通过填充0先占用未使用的byte空间，
        //这样可以让文件尽可能的占用连续的磁盘扇区，减少后续写入和读取文件时的磁盘寻道开销
        long newFileSize = calculateFileSizeWithPadding(fileChannel.position(), currentSize, preAllocSize);
        if (currentSize != newFileSize) {//将整个日志文件中未使用的部分填充0
            fileChannel.write((ByteBuffer) fill.position(0), newFileSize - fill.remaining());
            currentSize = newFileSize;
        }
        return currentSize;
    }

    /**
     * Calculates a new file size with padding. We only return a new size if
     * the current file position is sufficiently close (less than 4K) to end of
     * file and preAllocSize is > 0.
     *
     * @param position the point in the file we have written to
     * @param fileSize application keeps track of the current file size
     * @param preAllocSize how many bytes to pad
     * @return the new file size. It can be the same as fileSize if no
     * padding was done.
     * @throws IOException
     */
    // VisibleForTesting

    /***
     *
     * @param position 通过管道写入的字节长度
     * @param fileSize 文件大小
     * @param preAllocSize 与分配大小
     * @return
     */
    public static long calculateFileSizeWithPadding(long position, long fileSize, long preAllocSize) {
        // I如果剩余空间不足4k且预分配空间大于0
        if (preAllocSize > 0 && position + 4096 >= fileSize) {
            //如果已写入的长度超过了文件大小，文件大小扩为 写入的字节长度+预分配的大小
            if (position > fileSize){//刚创建的时候肯定走这个，这样就可以保证fileSize始终是preAllocSize的整数倍
                fileSize = position + preAllocSize;
                //这边会重新调整到预分配块长度的整数倍(是否是为了方便管理统计等？)
                fileSize -= fileSize % preAllocSize;
            } else {
                fileSize += preAllocSize;
            }
        }

        return fileSize;
    }

    /**
     * Find the log file that starts at, or just before, the snapshot. Return
     * this and all subsequent logs. Results are ordered by zxid of file,
     * ascending order.
     * @param logDirList array of files
     * @param snapshotZxid return files at, or before this zxid
     * @return
     */
    /***
     *
     * @param logDirList 日志文件列表
     * @param snapshotZxid  通过内存快照恢复的最大的事务id，剩余的比snapshotZxid就要从日志文件里恢复
     * @return 找出比包含有<=snapshotZxid的事务id的日志文件列表,当snapshotZxid=0时，获取所有的文件
     */
    public static File[] getLogFiles(File[] logDirList,long snapshotZxid) {
        //对日志文件进行排序，按照事务ID从高到低
        List<File> files = Util.sortDataDir(logDirList, LOG_FILE_PREFIX, true);
        long logZxid = 0;
        // Find the log file that starts before or at the same time as the
        // zxid of the snapshot
        for (File f : files) {
            long fzxid = Util.getZxidFromName(f.getName(), LOG_FILE_PREFIX);
            //如果文件名的事务id:fzxid>快照的最新的zxid
            if (fzxid > snapshotZxid) {
                continue;
            }
            //如果fzxid <= snapshotZxid && fzxid > logZxid
            if (fzxid > logZxid) {
                logZxid = fzxid;
            }
        }
        List<File> v=new ArrayList<File>(5);
        for (File f : files) {
            long fzxid = Util.getZxidFromName(f.getName(), LOG_FILE_PREFIX);
            if (fzxid < logZxid) {//找出文件id大于logZxid的文件名
                continue;
            }
            v.add(f);
        }
        return v.toArray(new File[0]);

    }

    /**
     * get the last zxid that was logged in the transaction logs
     * @return the last zxid logged in the transaction logs
     */
    //该方法只在节点服务器启动的时候被调用
    public long getLastLoggedZxid() {//从日志文件中获取最大的Zxid
        //找出所有的日志文件
        File[] files = getLogFiles(logDir.listFiles(), 0);
        //排序日志文件，并从日志文件名称上获取包含最大zxid的日志文件的文件名中的日志id
        long maxLog=files.length>0?
                Util.getZxidFromName(files[files.length-1].getName(),LOG_FILE_PREFIX):-1;

        // if a log file is more recent we must scan it to find
        // the highest zxid
        long zxid = maxLog;
        TxnIterator itr = null;
        try {
            FileTxnLog txn = new FileTxnLog(logDir);
            //根据文件名的事务id遍历迭代该日志文件，获取整个内存数据库的最大事务id,
            itr = txn.read(maxLog);
            while (true) {
                if(!itr.next())
                    break;
                TxnHeader hdr = itr.getHeader();
                zxid = hdr.getZxid();
            }
        } catch (IOException e) {
            LOG.warn("Unexpected exception", e);
        } finally {
            close(itr);
        }
        return zxid;
    }

    private void close(TxnIterator itr) {
        if (itr != null) {
            try {
                itr.close();
            } catch (IOException ioe) {
                LOG.warn("Error closing file iterator", ioe);
            }
        }
    }

    /**
     * commit the logs. make sure that everything hits the
     * disk
     */
    /***
     * 提交事务，确保日志刷新到磁盘中
     * @throws IOException
     */
    public synchronized void commit() throws IOException {
        if (logStream != null) {//刷新
            logStream.flush();
        }
        for (FileOutputStream log : streamsToFlush) {
            log.flush();
            if (forceSync) {//是否强制刷盘
                long startSyncNS = System.nanoTime();

                FileChannel channel = log.getChannel();
                channel.force(false);

                syncElapsedMS = TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - startSyncNS);
                if (syncElapsedMS > fsyncWarningThresholdMS) {
                    LOG.warn("fsync-ing the write ahead log in "
                            + Thread.currentThread().getName()
                            + " took " + syncElapsedMS
                            + "ms which will adversely effect operation latency. "
                            + "File size is " + channel.size() + " bytes. "
                            + "See the ZooKeeper troubleshooting guide");
                }
            }
        }
        while (streamsToFlush.size() > 1) {
            streamsToFlush.removeFirst().close();
        }
    }

    /**
     *
     * @return elapsed sync time of transaction log in milliseconds
     */
    public long getTxnLogSyncElapsedTime() {
        return syncElapsedMS;
    }

    /**
     * start reading all the transactions from the given zxid
     * @param zxid the zxid to start reading transactions from
     * @return returns an iterator to iterate through the transaction
     * logs
     */
    /***
     * 根据目标事务id，从日志文件中读取大于该事务id的事务，并返回这些事务构成的迭代器TxnIterator
     * 注意底层在遍历每一个日志文件的时候，会对文件进行魔数校验等，避免文件被损坏
     * @param zxid 迭代器的开始位置
     * @return
     * @throws IOException
     */
    public TxnIterator read(long zxid) throws IOException {
        return read(zxid, true);
    }

    /**
     * start reading all the transactions from the given zxid.
     *
     * @param zxid the zxid to start reading transactions from
     * @param fastForward true if the iterator should be fast forwarded to point
     *        to the txn of a given zxid, else the iterator will point to the
     *        starting txn of a txnlog that may contain txn of a given zxid
     * @return returns an iterator to iterate through the transaction logs
     */
    public TxnIterator read(long zxid, boolean fastForward) throws IOException {
        return new FileTxnIterator(logDir, zxid, fastForward);
    }

    /**
     * truncate the current transaction logs
     * @param zxid the zxid to truncate the logs to
     * @return true if successful false if not
     */
    /***
     * 清空大于zxid的事务日志
     * @param zxid
     * @return
     * @throws IOException
     */
    public boolean truncate(long zxid) throws IOException {
        FileTxnIterator itr = null;
        try {
            //找出大于zxid的事务迭代器
            itr = new FileTxnIterator(this.logDir, zxid);
            PositionInputStream input = itr.inputStream;
            if(input == null) {
                throw new IOException("No log files found to truncate! This could " +
                        "happen if you still have snapshots from an old setup or " +
                        "log files were deleted accidentally or dataLogDir was changed in zoo.cfg.");
            }
            long pos = input.getPosition();
            //
            RandomAccessFile raf=new RandomAccessFile(itr.logFile,"rw");
            raf.setLength(pos);
            raf.close();
            while(itr.goToNextLog()) {
                if (!itr.logFile.delete()) {
                    LOG.warn("Unable to truncate {}", itr.logFile);
                }
            }
        } finally {
            close(itr);
        }
        return true;
    }

    /**
     * read the header of the transaction file
     * @param file the transaction file to read
     * @return header that was read from the file
     * @throws IOException
     */
    private static FileHeader readHeader(File file) throws IOException {
        InputStream is =null;
        try {
            is = new BufferedInputStream(new FileInputStream(file));
            InputArchive ia=BinaryInputArchive.getArchive(is);
            FileHeader hdr = new FileHeader();
            hdr.deserialize(ia, "fileheader");
            return hdr;
         } finally {
             try {
                 if (is != null) is.close();
             } catch (IOException e) {
                 LOG.warn("Ignoring exception during close", e);
             }
         }
    }

    /**
     * the dbid of this transaction database
     * @return the dbid of this database
     */
    public long getDbId() throws IOException {
        FileTxnIterator itr = new FileTxnIterator(logDir, 0);
        FileHeader fh=readHeader(itr.logFile);
        itr.close();
        if(fh==null)
            throw new IOException("Unsupported Format.");
        return fh.getDbid();
    }

    /**
     * the forceSync value. true if forceSync is enabled, false otherwise.
     * @return the forceSync value
     */
    public boolean isForceSync() {
        return forceSync;
    }

    /**
     * a class that keeps track of the position
     * in the input stream. The position points to offset
     * that has been consumed by the applications. It can
     * wrap buffered input streams to provide the right offset
     * for the application.
     */
    static class PositionInputStream extends FilterInputStream {
        long position;
        protected PositionInputStream(InputStream in) {
            super(in);
            position = 0;
        }

        @Override
        public int read() throws IOException {
            int rc = super.read();
            if (rc > -1) {
                position++;
            }
            return rc;
        }

        public int read(byte[] b) throws IOException {
            int rc = super.read(b);
            if (rc > 0) {
                position += rc;
            }
            return rc;
        }

        @Override
        public int read(byte[] b, int off, int len) throws IOException {
            int rc = super.read(b, off, len);
            if (rc > 0) {
                position += rc;
            }
            return rc;
        }

        @Override
        public long skip(long n) throws IOException {
            long rc = super.skip(n);
            if (rc > 0) {
                position += rc;
            }
            return rc;
        }
        public long getPosition() {
            return position;
        }

        @Override
        public boolean markSupported() {
            return false;
        }

        @Override
        public void mark(int readLimit) {
            throw new UnsupportedOperationException("mark");
        }

        @Override
        public void reset() {
            throw new UnsupportedOperationException("reset");
        }
    }

    /**
     * this class implements the txnlog iterator interface
     * which is used for reading the transaction logs
     */
    public static class FileTxnIterator implements TxnLog.TxnIterator {
        File logDir;//日志文件存放目录
        //开始读取的起始zxid
        long zxid;//迭代器的开始zxid，也就是这个迭代器主要是用来存放比我们要查找的zxid大的事务
        TxnHeader hdr;//事务头
        Record record;
        File logFile;//
        InputArchive ia;
        static final String CRC_ERROR="CRC check failed";

        PositionInputStream inputStream=null;
        //存放包含比我们需要查找的zxid大的事务id的日志文件列表
        private ArrayList<File> storedFiles;

        /**
         * create an iterator over a transaction database directory
         * @param logDir 日志存放目录
         * @param zxid 开始读取的zxid
         * @param fastForward
         *              true:应该会快照向前查找，定位到zxid的txn
         *              false: 则迭代器指向可能包含给定的zxid的Txn的txnlog文件
         * @throws IOException
         */
        public FileTxnIterator(File logDir, long zxid, boolean fastForward)
                throws IOException {
            this.logDir = logDir;
            this.zxid = zxid;
            //过滤出所有需要读的日志文件，并利用goToNextLog()方法打开第一个日志日志文件的输入流
            init();
            if (fastForward && hdr != null) {
                while (hdr.getZxid() < zxid) {
                    if (!next())
                        break;
                }
            }
        }

        /**
         * initialize to the zxid specified
         * this is inclusive of the zxid
         * @throws IOException
         */
        void init() throws IOException {
            //storedFiles按照事务id从大到小排序
            storedFiles = new ArrayList<File>();
            //排序日志文件
            List<File> files = Util.sortDataDir(FileTxnLog.getLogFiles(logDir.listFiles(), 0), LOG_FILE_PREFIX, false);
            for (File f: files) {//迭代日志文件并找出可能存在事务id大于zxid的日志文件
                if (Util.getZxidFromName(f.getName(), LOG_FILE_PREFIX) >= zxid) {
                    storedFiles.add(f);
                }
                // 当执行到这步，说明后面的日志都比给定的zxid小，就没必要继续遍历，直接break
                else if (Util.getZxidFromName(f.getName(), LOG_FILE_PREFIX) < zxid) {
                    storedFiles.add(f);
                    break;
                }
            }
            //获打开第一个日志日志文件的输入流，也就是zxid最小的
            goToNextLog();
            //next方法用来从日志文件中读取一条记录，校验并反序列化出来，
            //读取成功返回true，如果读到了文件末尾则调goToNextLog()读下一个文件，以此递归直到最后
            next();
        }

        /**
         * Return total storage size of txnlog that will return by this iterator.
         */
        public long getStorageSize() {
            long sum = 0;
            for (File f : storedFiles) {
                sum += f.length();
            }
            return sum;
        }

        /**
         * go to the next logfile
         * @return true if there is one and false if there is no
         * new file to be read
         * @throws IOException
         */
        //打开第一个日志文件输入流
        private boolean goToNextLog() throws IOException {
            if (storedFiles.size() > 0) {
                this.logFile = storedFiles.remove(storedFiles.size()-1);
                ia = createInputArchive(this.logFile);
                return true;
            }
            return false;
        }

        /**
         * read the header from the inputarchive
         * @param ia the inputarchive to be read from
         * @param is the inputstream
         * @throws IOException
         */
        protected void inStreamCreated(InputArchive ia, InputStream is)
            throws IOException{
            FileHeader header= new FileHeader();
            header.deserialize(ia, "fileheader");
            if (header.getMagic() != FileTxnLog.TXNLOG_MAGIC) {
                throw new IOException("Transaction log: " + this.logFile + " has invalid magic number "
                        + header.getMagic()
                        + " != " + FileTxnLog.TXNLOG_MAGIC);
            }
        }

        /**
         * Invoked to indicate that the input stream has been created.
         * @param ia input archive
         * @param is file input stream associated with the input archive.
         * @throws IOException
         **/
        protected InputArchive createInputArchive(File logFile) throws IOException {
            if(inputStream==null){
                inputStream= new PositionInputStream(new BufferedInputStream(new FileInputStream(logFile)));
                LOG.debug("Created new input stream " + logFile);
                ia  = BinaryInputArchive.getArchive(inputStream);
                inStreamCreated(ia,inputStream);
                LOG.debug("Created new input archive " + logFile);
            }
            return ia;
        }

        /**
         * create a checksum algorithm
         * @return the checksum algorithm
         */
        protected Checksum makeChecksumAlgorithm(){
            return new Adler32();
        }

        /**
         * the iterator that moves to the next transaction
         * @return true if there is more transactions to be read
         * false if not.
         */
        //读取下一个事务，并检查事务的万完整性，包括事务头信息
        public boolean next() throws IOException {
            if (ia == null) {
                return false;
            }
            try {
                long crcValue = ia.readLong("crcvalue");
                byte[] bytes = Util.readTxnBytes(ia);
                // Since we preallocate, we define EOF to be an
                if (bytes == null || bytes.length==0) {
                    throw new EOFException("Failed to read " + logFile);
                }
                // 检查文件是否被破坏
                Checksum crc = makeChecksumAlgorithm();
                crc.update(bytes, 0, bytes.length);
                if (crcValue != crc.getValue())
                    throw new IOException(CRC_ERROR);
                hdr = new TxnHeader();
                //反序列事务信息
                record = SerializeUtils.deserializeTxn(bytes, hdr);
            } catch (EOFException e) {
                LOG.debug("EOF exception " + e);
                inputStream.close();
                inputStream = null;
                ia = null;
                hdr = null;
                // 执行到这边意味着文件已经读到末尾了，就要把留指向下一个文件
                if (!goToNextLog()) {
                    return false;
                }
                // if we went to the next log file, we should call next() again
                return next();
            } catch (IOException e) {
                inputStream.close();
                throw e;
            }
            return true;
        }

        /**
         * return the current header
         * @return the current header that
         * is read
         */
        public TxnHeader getHeader() {
            return hdr;
        }

        /**
         * return the current transaction
         * @return the current transaction
         * that is read
         */
        public Record getTxn() {
            return record;
        }

        /**
         * close the iterator
         * and release the resources.
         */
        public void close() throws IOException {
            if (inputStream != null) {
                inputStream.close();
            }
        }
    }

}
