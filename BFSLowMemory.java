import java.io.*;
import java.util.*;
/**
 * Same as BFS.java, but uses less memory and is suitable for computing larger BFS trees.
 * time: O( (# nodes in BFS tree) * ( (max depth of BFS tree) + (degree of each vertex)*(# pieces in target region to solve) ) )
 * memory: ~(# nodes in BFS tree)/4 bytes of disk space (2 bits per node)
 */
public class BFSLowMemory {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static boolean[] mask(String s) {
        boolean[] out=new boolean[s.length()];
        for (int i=0; i<s.length(); i++)
            out[i]=s.charAt(i)=='1';
        return out;
    }
    public static boolean[][] parseState(String s) {
        String[] pcs=s.split("x");
        if (pcs.length!=2) throw new RuntimeException("Not in 2 pieces: "+s);
        return new boolean[][] {mask(pcs[0]),mask(pcs[1])};
    }
    public int R, C, F;
    private boolean[] Rf, Cf;
    public int[] preblock;
    public int[] a2f, f2a;
    public int T;
    public int[] target;
    public long encode(int[] A) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i=F-1; i>=F-T; i--) {
            //swap idxs i and L[A[i-(F-T)]] in P
            int j=L[A[i-(F-T)]];
            int pi=P[i];//, pj=P[j];
            //P[i]=pj; //<--idx i will never be touched again
            P[j]=pi;
            L[pi]=j;
            //L[pj]=i;
            //J_i==j
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    public long encodeprod(int[] A, int[] B) { //computes encode(prod(A,B)), where prod(A,B)[i]:=A[B[i]] for all i
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i=F-1; i>=F-T; i--) {
            int j=L[A[B[i-(F-T)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    public int[] decode(long code) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        for (int v=F; v>F-T; v--) {
            int i=v-1, j=(int)(code%v);
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        return Arrays.copyOfRange(P,F-T,F);
    }
    private void printScramble(long code) {
        int[] board=new int[R*C]; Arrays.fill(board,-1);
        for (int p:preblock) board[p]=-2;
        int[] locs=decode(code);
        for (int t=0; t<T; t++) board[f2a[locs[t]]]=target[t];
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++) {
                int v=board[r*C+c];
                if (R*C<=26) System.out.print(v==-2?"#":v==-1?".":(char)(v+'A'));
                else System.out.printf("%3s",v==-2?"#":v==-1?".":v);
            }
            System.out.println();
        }
    }

    public int M;
    public int[][] mvfactions;
    public long ncombos;
    public String state0, state1;
    public BFSLowMemory(String state0, String state1) {
        this.state0=state0; this.state1=state1;
        boolean[][] S0=parseState(state0), S1=parseState(state1);
        Rf=S0[0]; Cf=S0[1];
        R=Rf.length; C=Cf.length;
        if (S1[0].length!=R||S1[1].length!=C) throw new RuntimeException("Mismatching dimensions for start and end state: "+state0+"-->"+state1);
        F=0; f2a=new int[R*C]; a2f=new int[R*C]; Arrays.fill(a2f,-1);
        T=0; target=new int[R*C];
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (Rf[r]||Cf[c]) {
            int l=r*C+c;
            a2f[l]=F; f2a[F]=l;
            if (!S1[0][r]&&!S1[1][c]) target[T++]=l;
            F++;
        }
        preblock=new int[R*C]; {
            int K=0;
            for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (!Rf[r]&&!Cf[c]) preblock[K++]=r*C+c;
            preblock=Arrays.copyOf(preblock,K);
        }
        f2a=Arrays.copyOf(f2a,F); target=Arrays.copyOf(target,T);
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                        Rf[r]||Cf[c]?
                                ((S1[0][r]||S1[1][c]?"":"'")+a2f[r*C+c]):
                                "#"
                        //': piece that this BFS tree tries to solve; *: gripped piece
                );
            System.out.println();
        }
        System.out.printf("f2a=%s%na2f%s%ntarget=%s%n",Arrays.toString(f2a),Arrays.toString(a2f),Arrays.toString(target));

        //generate every single-cost move that does not disturb pieces in the preblock
        mvfactions=new int[2*R*C][]; {
            M=0;
            for (int t=0; t<2; t++)
                for (int co=0; co<(t==0?R:C); co++) if ((t==0?Rf:Cf)[co])
                    for (int s=-1; s<=1; s+=2) {
                        mvfactions[M]=new int[F];
                        for (int f=0; f<F; f++) {
                            int r=f2a[f]/C, c=f2a[f]%C;
                            mvfactions[M][f]=a2f[t==0?(r*C+(r==co?mod(c+s,C):c)):(c==co?mod(r+s,R):r)*C+c];
                        }
                        M++;
                    }
            mvfactions=Arrays.copyOf(mvfactions,M);
        }
    }

    private static void set(byte[] A, long pos) {
        A[(int)(pos/8)]|=((byte)1)<<(pos%8);
    }
    private static void rem(byte[] A, long pos) {
        A[(int)(pos/8)]&=~(((byte)1)<<(pos%8));
    }
    private static boolean isset(byte[] A, long pos) {
        return ((A[(int)(pos/8)]>>(pos%8))&1)!=0;
    }
    private static final long CHUNK=1_000_000;
    private static void initBitset(String file, long S) throws IOException {
        BufferedOutputStream fout=new BufferedOutputStream(new FileOutputStream(file));
        long B=S/8+1;
        for (long b=0; b<B; b+=CHUNK)
            fout.write(new byte[(int)(Math.min(b+CHUNK,B)-b)]);
        fout.close();
    }
    private static byte[] segment(RandomAccessFile f, long blo, long bhi) throws IOException {
        byte[] data=new byte[(int)(bhi-blo)];
        f.seek(blo);
        f.readFully(data);
        return data;
    }
    private long addConditionally(RandomAccessFile f, RandomAccessFile condition, long S, long[] vals) throws IOException {
        long B=S/8+1;
        long out=0;
        long[][] bins=new long[(int)(B/CHUNK)+1][];
        int[] binSizes=new int[bins.length];
        for (long v:vals) binSizes[(int)(v/8/CHUNK)]++;
        for (int c=0; c<bins.length; c++) bins[c]=new long[binSizes[c]];
        Arrays.fill(binSizes,0);
        for (long v:vals) {
            int c=(int)(v/8/CHUNK);
            bins[c][binSizes[c]++]=v;
        }
        for (long blo=0; blo<B; blo+=CHUNK) if (bins[(int)(blo/CHUNK)].length>0) {
            long bhi=Math.min(blo+CHUNK,B);
            byte[] fs=null, ss=segment(condition,blo,bhi);
            for (long v:bins[(int)(blo/CHUNK)])
                if (!isset(ss,v-blo*8)) {
                    if (fs==null) fs=segment(f,blo,bhi);
                    if (!isset(fs,v-blo*8)) out++;
                    set(fs,v-blo*8);
                }
            if (fs!=null) {
                f.seek(blo); f.write(fs);
            }
        }
        return out;
    }
    public void bfs(String supfolder, int buffer) throws IOException {
        System.out.println("buffer="+buffer+", CHUNK="+CHUNK);
        ncombos=1;
        for (int rep=0; rep<T; rep++) ncombos*=F-rep;
        System.out.println("ncombos="+ncombos);

        //BFS
        //we store the set of all nodes currently in our BFS tree,
        // and the set of all nodes waiting to have their neighbors explored,
        // as large bitsets stored in binary files
        long B=ncombos/8+1;
        String folder=String.format("%s/%dx%d-%s-%s/",supfolder,R,C,state0,state1);
        new File(folder).mkdirs();
        String fseen=folder+"seen.bin", ffront=folder+"front.bin";
        initBitset(fseen,ncombos);
        initBitset(ffront,ncombos);
        RandomAccessFile seen=new RandomAccessFile(fseen,"rw"), front=new RandomAccessFile(ffront,"rw"); {
            long v=encodeprod(a2f,target);
            front.seek(v/8); byte y=front.readByte(); y|=1<<(v%8); front.seek(v/8); front.write(y);
        }
        long reached=1;
        System.out.printf("%d:%d%n",0,1);
        long st=System.currentTimeMillis(), mark=0;
        long nwrites=0;
        long[] times=new long[4];
        for (int D=1;; D++) {
            //mark all nodes in current front as "seen" before actually processing them
            //this is so when actually expanding each front node to its new neighbors,
            //those neighbors will be considered in the front but not seen,
            //and we can distinguish between nodes in our current front and nodes in our next front
            /*
            bit(seen,f)    bit(infront,f)  meaning
            0                   0               not visited
            0                   1               in the next front
            1                   0               already processed
            1                   1               in our current front, waiting to be processed (expanded to its neighbors)
             */

            //set all "01" nodes to "11" nodes, i.e. mark all nodes in our front as in our current front (and not the future front)
            times[0]-=System.currentTimeMillis();
            for (long blo=0; blo<B; blo+=CHUNK) {
                long bhi=Math.min(blo+CHUNK,B);
                byte[] fdata=segment(front,blo,bhi), sdata=segment(seen,blo,bhi);
                for (long b=blo; b<bhi; b++) if (fdata[(int)(b-blo)]!=0) {
                    for (long f=b*8; f<b*8+8; f++) if (isset(fdata,f-blo*8))
                        set(sdata,f-blo*8);
                }
                seen.seek(blo); seen.write(sdata);
            }
            times[0]+=System.currentTimeMillis();

            //explore neighbors of nodes on current front
            times[1]-=System.currentTimeMillis();
            long fcnt=0, cnt=0;
            long[] nfront=new long[buffer]; int nfsz=0;
            for (long blo=0; blo<B; blo+=CHUNK) {
                long bhi=Math.min(blo+CHUNK,B);
                byte[] fdata=segment(front,blo,bhi), sdata=segment(seen,blo,bhi);
                for (long b=blo; b<bhi; b++) if ((fdata[(int)(b-blo)]&sdata[(int)(b-blo)])!=0)
                for (long f=b*8; f<b*8+8; f++) if (isset(fdata,f-blo*8) && isset(sdata,f-blo*8)) {
                    fcnt++;
                    if ((fcnt&127)==0) {
                        long t=System.currentTimeMillis()-st;
                        if (t>=mark) {
                            if (mark>0) System.out.printf("%d %d t=%d%n",fcnt,cnt,t);
                            mark+=100_000;
                        }
                    }
                    int[] scrm=decode(f);
                    for (int mi=0; mi<M; mi++) {
                        nfront[nfsz++]=encodeprod(mvfactions[mi],scrm);
                        if (nfsz>=buffer) {
                            nwrites++;
                            times[2]-=System.currentTimeMillis();
                            cnt+=addConditionally(front,seen,ncombos,nfront);
                            times[2]+=System.currentTimeMillis();
                            nfsz=0;
                        }
                    }
                }
            }
            cnt+=addConditionally(front,seen,ncombos,Arrays.copyOf(nfront,nfsz));
            times[1]+=System.currentTimeMillis();

            if (cnt==0) {
                PrintWriter antipodesOut=new PrintWriter(folder+"antipodes.txt");
                for (long blo=0; blo<B; blo+=CHUNK) {
                    long bhi=Math.min(blo+CHUNK,B);
                    byte[] fdata=segment(front,blo,bhi), sdata=segment(seen,blo,bhi);
                    for (long b=blo; b<bhi; b++) if ((fdata[(int)(b-blo)]&sdata[(int)(b-blo)])!=0)
                    for (long f=b*8; f<b*8+8; f++) if (isset(fdata,f-blo*8) && isset(sdata,f-blo*8))
                        antipodesOut.println(f);
                }
                antipodesOut.close();
                break;
            }
            System.out.printf("%d:%d t=%d%n",D,cnt,System.currentTimeMillis()-st);
            reached+=cnt;

            times[3]-=System.currentTimeMillis();
            for (long blo=0; blo<B; blo+=CHUNK) {
                long bhi=Math.min(blo+CHUNK,B);
                byte[] fdata=segment(front,blo,bhi), sdata=segment(seen,blo,bhi);
                for (long b=blo; b<bhi; b++) if ((fdata[(int)(b-blo)]&sdata[(int)(b-blo)])!=0)
                for (long f=b*8; f<b*8+8; f++) if (isset(fdata,f-blo*8) && isset(sdata,f-blo*8))
                    rem(fdata,f-blo*8);
                front.seek(blo); front.write(fdata);
            }
            times[3]+=System.currentTimeMillis();
        }
        System.out.println("\n#reached="+reached+"\ntotal BFS time="+(System.currentTimeMillis()-st));
        System.out.println("running times for [marking front nodes, expanding, writing new front nodes, removing front nodes]="+Arrays.toString(times));
        System.out.println("# calls to add2Bitset()="+nwrites);
    }

    public static void main(String[] args) throws IOException {
        new BFSLowMemory("010101x010101","000101x000101").bfs("BFSLowMemory",100_000_000);
    }
}
