import java.io.*;
import java.util.*;

public class BFSLargeFile {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    public static String mvnameStr(int[] mvn) {
        return (mvn[0]==0?"R":"C")+mvn[1]+(mvn[2]==-1?"'":mvn[2]==1?"":("^"+mvn[2]));
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
    private static int[] prod(int[] A, int[] B) { //return [ A[B[i]] for all i ]
        int[] out=new int[B.length];
        for (int i=0; i<B.length; i++) out[i]=A[B[i]];
        return out;
    }
    //define absolute indexing as mapping coordinate (r,c) to index r*C+c
    //every scramble is represented by an array L[], where piece i is at location L[i]
    private String description;
    public int R, C;
    private int F;
    public boolean[] Rf, Cf;
    public int[] preblock;
    //cell (r,c) is free iff Rf[r]||Cf[c]
    public int[] tofree, freeto;
    //tofree[r*C+c]=i, where (r,c) is the i-th free cell
    //  i.e. i is the "free coordinate" of (r,c)
    //the "absolute coordinate" of cell (r,c) is rC+c
    public int T;
    public int[] target; //list of pieces this tree tries to solve, in absolute indexing
    public int M;
    public int[][] mvfactions, mvnames;
    public BFSLargeFile(String state0, String state1) {
        boolean[][] S0=parseState(state0), S1=parseState(state1);
        Rf=S0[0]; Cf=S0[1];
        R=Rf.length; C=Cf.length;
        if (S1[0].length!=R||S1[1].length!=C) throw new RuntimeException("Mismatching dimensions for start and end state: "+state0+"-->"+state1);
        F=0; freeto=new int[R*C]; tofree=new int[R*C]; Arrays.fill(tofree,-1);
        T=0; target=new int[R*C];
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (Rf[r]||Cf[c]) {
            int l=r*C+c;
            tofree[l]=F; freeto[F]=l;
            if (!S1[0][r]&&!S1[1][c]) target[T++]=l;
            F++;
        }
        preblock=new int[R*C]; {
            int K=0;
            for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (!Rf[r]&&!Cf[c]) preblock[K++]=r*C+c;
            preblock=Arrays.copyOf(preblock,K);
        }
        freeto=Arrays.copyOf(freeto,F); target=Arrays.copyOf(target,T);
        //for (int[] a:new int[][] {freeto,tofree,target}) System.out.println(Arrays.toString(a));
        {
            StringBuilder s=new StringBuilder(state0+"-->"+state1+"\n");
            for (int r=0; r<R; r++) {
                for (int c=0; c<C; c++)
                    s.append(String.format("%4s",
                            Rf[r]||Cf[c]?
                                    ((S1[0][r]||S1[1][c]?"":"'")+tofree[r*C+c]):
                                    "X"
                            //': piece that this BFS tree tries to solve; *: gripped piece
                    ));
                s.append('\n');
            }
            description=s.toString();
        }

        //moves: every move is represented with [t,a,r]:
        //t: type (0=row shift, 1=clm shift)
        //a: the a-th (row if t==0, else clm)
        //r: # units to shift (right if t==0, else down)
        mvnames=new int[2*R*C][]; mvfactions=new int[2*R*C][]; {
            M=0;
            for (int t=0; t<2; t++)
                for (int co=0; co<(t==0?R:C); co++) if ((t==0?Rf:Cf)[co])
                    for (int s=-1; s<=1; s+=2) {
                        mvnames[M]=new int[] {t,co,s};
                        mvfactions[M]=new int[F];
                        for (int i=0; i<F; i++) {
                            int r=freeto[i]/C, c=freeto[i]%C;
                            mvfactions[M][i]=tofree[t==0?(r*C+(r==co?mod(c+s,C):c)):(c==co?mod(r+s,R):r)*C+c];
                        }
                        M++;
                    }
            mvnames=Arrays.copyOf(mvnames,M);
            mvfactions=Arrays.copyOf(mvfactions,M);
        }
        ncombos=1;
        for (int rep=0; rep<T; rep++) ncombos*=F-rep;
        nbytes=0;
        while (ncombos>(1L<<(8*nbytes))) nbytes++;
    }
    public long ncombos;
    private int nbytes;
    private long[] visited;
    private PrintWriter fout;
    private void add(long n) {
        visited[(int)(n/64)]|=1L<<(n%64);
    }
    private boolean contains(long n) {
        return (visited[(int)(n/64)]&(1L<<(n%64)))!=0;
    }
    private void addn(BufferedOutputStream f, long v) throws IOException {
        for (int b=0; b<nbytes; b++) f.write((byte)(v>>(8*b)));
    }
    private void println(String s) {
        System.out.println(s);
        fout.println(s);
    }
    public void bfs(String folder) throws IOException {
        long st=System.currentTimeMillis();
        new File(folder).mkdirs();
        fout=new PrintWriter(new FileWriter(folder+"/description.txt"));
        println(description+"ncombos="+ncombos);
        {
            long n=ncombos/64+1;
            if (n>Integer.MAX_VALUE) throw new RuntimeException("Too many elements for long[] set: "+n);
            visited=new long[(int)n];
        }
        {
            long solvedcode=encode(prod(tofree,target));
            BufferedOutputStream f=new BufferedOutputStream(new FileOutputStream(folder+"/0.bin"));
            add(solvedcode); addn(f,solvedcode);
            f.close();
        }
        long tot=0;
        for (int D=0;; D++) {
            long cnt=0;
            BufferedInputStream front=new BufferedInputStream(new FileInputStream(folder+"/"+D+".bin"));
            BufferedOutputStream nfront=new BufferedOutputStream(new FileOutputStream(folder+"/"+(D+1)+".bin"));
            for (;; cnt++) {
                byte[] bs=new byte[nbytes];
                if (front.read(bs)<nbytes) break;
                long code=0;
                for (int i=0; i<nbytes; i++)
                    code|=Byte.toUnsignedLong(bs[i])<<(8*i);
                int[] scrm=decode(code);
                for (int m=0; m<M; m++) {
                    long nf=encode(scrm,mvfactions[m]);
                    if (!contains(nf)) {
                        add(nf);
                        addn(nfront,nf);
                    }
                }
            }
            nfront.close();
            if (cnt==0) break;
            println(D+":"+cnt);
            tot+=cnt;
        }
        println("tot="+tot+"\ntime="+(System.currentTimeMillis()-st));
        fout.close();
    }
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
    public long encode(int[] A, int[] f) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i=F-1; i>=F-T; i--) {
            int j=L[f[A[i-(F-T)]]];
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
    public static void main(String[] args) throws IOException {
        new BFSLargeFile("000011x000011","000001x000001").bfs("BFSLargeFile/test");
    }
}
//NOTE: run using command line with flag -Xmx10g or something (64-bit JVM required)
