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

    private static final int CHUNK=1_000_000;
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
        String fseen=folder+"mask0.bin", ffront=folder+"mask1.bin";
        initBitset(fseen,ncombos);
        initBitset(ffront,ncombos);
        RandomAccessFile mask0=new RandomAccessFile(fseen,"rw"), mask1=new RandomAccessFile(ffront,"rw"); {
            long v=encodeprod(a2f,target);
            mask0.seek(v/8); byte x=mask0.readByte(); x|=1<<(v%8); mask0.seek(v/8); mask0.write(x);
            mask1.seek(v/8); byte y=mask1.readByte(); y|=1<<(v%8); mask1.seek(v/8); mask1.write(y);
        }
        long[] times=new long[4];
        System.out.println("t_stats=[expanding, adding new front nodes, modifying bytes with new front nodes, reorganizing front nodes]");
        class Updater {
            int nbins=(int)(B/CHUNK)+1, binsz=buffer/nbins+1;
            long[][] bins=new long[nbins][binsz];
            int[] binIdxs=new int[nbins];
            long nbinwrites=0;
            private long add(long v) throws IOException {
                int k=(int)(v/8/CHUNK);
                bins[k][binIdxs[k]++]=v;
                return binIdxs[k]==binsz?writeBin(k):0;
            }
            private long writeBin(int k) throws IOException {
                times[1]-=System.currentTimeMillis();
                long blo=k*(long)CHUNK, bhi=Math.min(blo+CHUNK,B);
                byte[] data0=segment(mask0,blo,bhi), data1=segment(mask1,blo,bhi);
                times[2]-=System.currentTimeMillis();
                int out=0;
                //if (data0[i],data1[i])==(0,0), change it to (0,1)
                for (int i=0; i<binIdxs[k]; i++) {
                    long v=bins[k][i];
                    int bi=(int)(v/8-blo);
                    byte c=(byte)(data0[bi]|data1[bi]);
                    int r=(int)(v%8);
                    if (((c>>r)&1)==0) {
                        data1[bi]|=1<<r;
                        out++;
                    }
                }
                times[2]+=System.currentTimeMillis();
                mask1.seek(blo); mask1.write(data1);
                binIdxs[k]=0;
                nbinwrites++;
                times[1]+=System.currentTimeMillis();
                return out;
            }
        } Updater $=new Updater();

        long reached=1;
        long st=System.currentTimeMillis(), mark=0;
        System.out.printf("%d:%d%n",0,1);
        StringBuilder distrStr=new StringBuilder("0:1\n");
        for (int D=1;; D++) {
            //bit(mask0,f)    bit(mask1,f)  meaning
            //0               0               not visited
            //1               0               already processed
            //0               1               in the next front
            //1               1               in our current front

            //explore neighbors of nodes on current mask1
            times[0]-=System.currentTimeMillis();
            long fcnt=0, cnt=0;
            Arrays.fill($.binIdxs,0);
            for (long blo=0; blo<B; blo+=CHUNK) {
                long bhi=Math.min(blo+CHUNK,B);
                byte[] data0=segment(mask0,blo,bhi), data1=segment(mask1,blo,bhi);
                for (int bi=0; bi<bhi-blo; bi++) {
                    byte c=(byte)(data0[bi]&data1[bi]);
                    if (c!=0) for (int r=0; r<8; r++) if (((c>>r)&1)!=0) {
                        fcnt++;
                        if ((fcnt&127)==0) {
                            long t=System.currentTimeMillis()-st;
                            if (t>=mark) {
                                if (mark>0) {
                                    long tmp=System.currentTimeMillis();
                                    times[0]+=tmp;
                                    System.out.printf("%d %d t=%d t_stats=%s%n",fcnt,cnt,t,Arrays.toString(times));
                                    times[0]-=tmp;
                                }
                                mark+=100_000;
                            }
                        }

                        int[] scrm=decode((blo+bi)*8+r);
                        for (int mi=0; mi<M; mi++)
                            cnt+=$.add(encodeprod(mvfactions[mi],scrm));
                    }
                }
            }
            for (int k=0; k<$.nbins; k++) if ($.binIdxs[k]>0)
                cnt+=$.writeBin(k);
            times[0]+=System.currentTimeMillis();

            if (cnt==0) {
                PrintWriter antipodesOut=new PrintWriter(folder+"antipodes.txt");
                for (long blo=0; blo<B; blo+=CHUNK) {
                    long bhi=Math.min(blo+CHUNK,B);
                    byte[] data0=segment(mask0,blo,bhi), data1=segment(mask1,blo,bhi);
                    for (int bi=0; bi<bhi-blo; bi++) {
                        byte c=(byte)(data0[bi]&data1[bi]);
                        if (c!=0) for (int r=0; r<8; r++) if (((c>>r)&1)!=0)
                            antipodesOut.println((blo+bi)*8+r);
                    }
                }
                antipodesOut.close();
                break;
            }
            reached+=cnt;

            //remove current front nodes from front, and set nodes in next front to nodes in current front
            times[3]-=System.currentTimeMillis();
            for (long blo=0; blo<B; blo+=CHUNK) {
                long bhi=Math.min(blo+CHUNK,B);
                byte[] data0=segment(mask0,blo,bhi), data1=segment(mask1,blo,bhi);
                //for bit position i, (data0[i],data1[i])==...
                //  (0,1): change to (1,1)
                //  (1,1): change to (1,0)
                //  anything else: do not change
                //  i.e. (0,0) and (1,0) do not change
                //then: if data0[i]==set, clear data1[i]
                //      if data1[i]==set, set data0[i]
                for (int bi=0; bi<bhi-blo; bi++) {
                    byte d0=data0[bi], d1=data1[bi];
                    data1[bi]&=~d0;
                    data0[bi]|=d1;
                }
                mask1.seek(blo); mask1.write(data1);
                mask0.seek(blo); mask0.write(data0);
            }
            times[3]+=System.currentTimeMillis();

            System.out.printf("%d:%d t=%d t_stats=%s%n",D,cnt,System.currentTimeMillis()-st,Arrays.toString(times));
            distrStr.append(D).append(":").append(cnt).append("\n");
        }
        {
            PrintWriter distrOut=new PrintWriter(folder+"distr.txt");
            distrOut.print(distrStr);
            distrOut.close();
        }
        System.out.printf("%nreached=%d%ntotal BFS time=%d%nt_stats=%s%n",reached,System.currentTimeMillis()-st,Arrays.toString(times));
        System.out.println("# bin writes="+$.nbinwrites);
    }

    public static void main(String[] args) throws IOException {
        new BFSLowMemory("001001x001001","000001x000001").bfs("BFSLowMemory",100_000_000);
    }
}
