import java.util.*;
public class LoopoverBFS {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static boolean[] mask(String s) {
        boolean[] out=new boolean[s.length()];
        for (int i=0; i<s.length(); i++)
            out[i]=s.charAt(i)=='1';
        return out;
    }
    //define absolute indexing as mapping coordinate (r,c) to index r*C+c
    //every scramble is represented by an array L[], where piece i is at location L[i]
    private int R, C;
    private int Nfree;
    private boolean[] Rfree, Cfree;
    //a location (r,c) is free iff Rfree[r]||Cfree[c]
    private int[] tofree, freeto;
    //tofree[r*C+c]=i, where free location (r,c) is assigned to index i
    public int K;
    private int[] solvedscrm;
    public int[] pcstosolve; //list of pieces this tree tries to solve, in absolute indexing
    private int solvedscrmcode;
    private int[][] mvactions, mvs;
    public static int[][] mvreduc(int[][] mvs) {
        int M=mvs.length;
        //move sequence reduction
        //when doing two moves of the same type, one after the other: [t,a,r], [t,b,s]:
        //WLOG a<=b, or else the two moves can be arranged to satisfy this condition without changing the final scramble
        //if a==b, then r+s!=0, else the two moves cancel each other out
        int[][] mvreduc=new int[M+1][];
        for (int m=0; m<M; m++) {
            List<Integer> l=new ArrayList<>();
            for (int m2=0; m2<M; m2++)
                if (mvs[m][0]!=mvs[m2][0]
                        ||mvs[m][1]<mvs[m2][1]
                        ||(mvs[m][1]==mvs[m2][1]&&mvs[m][2]+mvs[m2][2]!=0))
                    l.add(m2);
            mvreduc[m]=new int[l.size()];
            for (int i=0; i<l.size(); i++)
                mvreduc[m][i]=l.get(i);
        }
        mvreduc[M]=new int[M];
        for (int i=0; i<M; i++) mvreduc[M][i]=i;
        return mvreduc;
    }
    private int M;
    public int ncombos;
    //bfs stuff
    private long[] data;
    public int D;
    //c-->(depth,move from parent combo to c,parent combo)
    private long compressed(int depth, int parent, int move) {
        return ((long)depth*M+move)*ncombos+parent;
    }
    public int depth(int code) {
        return data[code]==-1?-1:(int)(data[code]/ncombos/M);
    }
    private int par(int code) {
        return data[code]==-1?-1:(int)(data[code]%ncombos);
    }
    private int mvi(int code) {
        return data[code]==-1?-1:(int)((data[code]/ncombos)%M);
    }
    public LoopoverBFS(int R, int C, String rf0, String cf0, String rf1, String cf1) {
        long st=System.currentTimeMillis();
        this.R=R; this.C=C;
        Rfree=mask(rf0); Cfree=mask(cf0);
        tofree=new int[R*C]; freeto=new int[R*C];
        Nfree=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if (Rfree[r]||Cfree[c]) {
                    tofree[r*C+c]=Nfree;
                    freeto[Nfree]=r*C+c;
                    Nfree++;
                }
                else tofree[r*C+c]=-1;
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%3d",tofree[r*C+c]);
            System.out.println();
        }
        boolean[] Rnfree=mask(rf1), Cnfree=mask(cf1);
        K=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    K++;
        solvedscrm=new int[K];
        for (int r=0, idx=0; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    solvedscrm[idx++]=tofree[r*C+c];
        pcstosolve=new int[K];
        for (int i=0; i<K; i++)
            pcstosolve[i]=freeto[solvedscrm[i]];
        System.out.println(Arrays.toString(solvedscrm));
        {
            long tmp=1;
            for (int rep=0; rep<K; rep++) tmp*=Nfree-rep;
            if (tmp>400_000_000) throw new RuntimeException("Too many combinations to handle.");
            ncombos=(int)tmp;
        }
        System.out.println("ncombos="+ncombos);

        //moves: every move is represented with [t,a,r]:
        //t: type (0=row shift, 1=clm shift)
        //a: the a-th (row if t==0, else clm)
        //r: # units to shift (right if t==0, else down)
        M=0;
        for (boolean b:Rfree) if (b) M+=2;
        for (boolean b:Cfree) if (b) M+=2;
        mvactions=new int[M][]; mvs=new int[M][]; {
            //mvactions[m][i]=free loc. that i-th free loc. will go to after move m is applied
            int idx=0;
            for (int mr=0; mr<R; mr++)
                if (Rfree[mr])
                    for (int s=-1; s<=1; s+=2) {
                        mvs[idx]=new int[] {0,mr,s};
                        mvactions[idx]=new int[Nfree];
                        for (int r=0; r<R; r++)
                            for (int c=0; c<C; c++)
                                if (Rfree[r]||Cfree[c])
                                    mvactions[idx][tofree[r*C+c]]=tofree[r*C+(r==mr?mod(c+s,C):c)];
                        idx++;
                    }
            for (int mc=0; mc<C; mc++)
                if (Cfree[mc])
                    for (int s=-1; s<=1; s+=2) {
                        mvs[idx]=new int[] {1,mc,s};
                        mvactions[idx]=new int[Nfree];
                        for (int r=0; r<R; r++)
                            for (int c=0; c<C; c++)
                                if (Rfree[r]||Cfree[c])
                                    mvactions[idx][tofree[r*C+c]]=tofree[(c==mc?mod(r+s,R):r)*C+c];
                        idx++;
                    }
        }
        //move sequence reduction
        //when doing two moves of the same type, one after the other: [t,a,r], [t,b,s]:
        //WLOG a<=b, or else the two moves can be arranged to satisfy this condition without changing the final scramble
        //if a==b, then r+s!=0, else the two moves cancel each other out
        int[][] mvreduc=mvreduc(mvs);
        //BFS
        data=new long[ncombos]; Arrays.fill(data,-1);
        int[] bfsList=new int[ncombos]; int fsz=0;
        bfsList[fsz++]=solvedscrmcode=comboCode(solvedscrm);
        data[bfsList[0]]=0;
        int fi;
        for (D=0, fi=0; fi<fsz; D++) {
            System.out.println(D+":"+(fsz-fi));
            for (int sz=fsz; fi<sz; fi++) {
                int f=bfsList[fi];
                int[] scrm=codeCombo(f);
                int[] mvlist=mvreduc[fi>0?mvi(f):M];
                for (int mi:mvlist) {
                    int nf=comboCode(scrm,mvactions[mi]);
                    if (data[nf]==-1) {
                        data[nf]=compressed(D+1,f,mi);
                        bfsList[fsz++]=nf;
                    }
                }
            }
        }
        System.out.println("#reached="+fsz);
        System.out.println("D="+D);
        System.out.println("total time="+(System.currentTimeMillis()-st));
    }
    /*
    encoding ordered combinations
    A[0]...A[K-1], 0<=A[i]<N, all A[i] distinct
    possible to transform permutation [0...N-1] into [....|A]
    using a sequence of swaps (i,J_i) for i=N-1 to N-K inclusive
      --> encode A as J_(N-1)+N*(J_(N-2)+(N-1)*(...+(N-K+2)*J_(N-K)...)
    for this program, N=Nfree, K=K
    */
    private int comboCode(int[] A) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=Nfree-1, pow=1; i>=Nfree-K; i--) {
            //swap idxs i and L[A[i-(N-K)]] in P
            int j=L[A[i-(Nfree-K)]];
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
    private int comboCode(int[] A, int[] f) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=Nfree-1, pow=1; i>=Nfree-K; i--) {
            int j=L[f[A[i-(Nfree-K)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    private int[] codeCombo(int code) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        for (int v=Nfree; v>Nfree-K; v--) {
            int i=v-1, j=code%v;
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[K];
        System.arraycopy(P,Nfree-K,out,0,K);
        return out;
    }
    //in all below methods, scrm is defined s.t. scrm[i]=location that pc i goes to, in absolute indexing
    public int depth(int[] scrm) {
        return depth(comboCode(scrm,tofree));
    }
    public int[] solveaction(int[] scrm) {
        return solveaction(comboCode(scrm,tofree));
    }
    public List<int[]> solvemvs(int[] scrm) {
        return solvemvs(comboCode(scrm,tofree));
    }
    public int[] solveaction(int code) {
        int[] out=new int[Nfree];
        for (int i=0; i<Nfree; i++) out[i]=i;
        for (int c=code; c!=solvedscrmcode; c=par(c)) {
            int[] mva=inv(mvactions[mvi(c)]);
            int[] nout=new int[Nfree];
            for (int i=0; i<Nfree; i++)
                nout[i]=mva[out[i]];
            out=nout;
        }
        return mva2abs(out);
    }
    public List<int[]> solvemvs(int code) {
        List<int[]> out=new ArrayList<>();
        for (int c=code; c!=solvedscrmcode; c=par(c)) {
            int[] mv=mvs[mvi(c)];
            out.add(new int[] {mv[0],mv[1],-mv[2]});
        }
        return out;
    }
    private static int[] inv(int[] P) {
        //return inverse permutation of P
        int[] I=new int[P.length];
        for (int i=0; i<P.length; i++)
            I[P[i]]=i;
        return I;
    }
    private int[] mva2abs(int[] mva) {
        //convert mva to array A
        //where A[a]=b describes absolute location a being shifted to absolute location b
        int[] out=new int[R*C];
        for (int a=0; a<R*C; a++)
            out[a]=tofree[a]==-1?a:freeto[mva[tofree[a]]];
        return out;
    }
}
