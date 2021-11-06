import java.util.*;
public class BFS {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    public static String mvseqStr(List<int[]> S) {
        StringBuilder str=new StringBuilder();
        for (int[] m:S)
            str.append(" ").append(m[0]==0?"R":"C").append(m[1]).append(m[2]==1?" ":m[2]==-1?"'":("("+m[2]+")"));
        return str.substring(1);
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
    public int R, C;
    private int F;
    public boolean[] Rf, Cf;
    //cell (r,c) is free iff Rf[r]||Cf[c]
    public int[] tofree, freeto;
    //tofree[r*C+c]=i, where (r,c) is the i-th free cell
    //  i.e. i is the "free coordinate" of (r,c)
    //the "absolute coordinate" of cell (r,c) is rC+c
    public int T;
    public int[] target; //list of pieces this tree tries to solve, in absolute indexing
    public int M;
    public int[][] mvactions, mvs, mvreduc;
    private boolean mvokay(int mai, int mbi) {
        int[] mva=mvs[mai], mvb=mvs[mbi];
        return mva[0]!=mvb[0]||mva[1]<mvb[1]
                ||(mva[1]==mvb[1]&&mva[2]+mvb[2]!=0);
    }
    public int ncombos;
    //bfs stuff
    private long[] data;
    public List<int[]> fronts; //BFS fronts
    public int diam; //depth of BFS tree
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
    public BFS(String state0, String state1) {
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
        freeto=Arrays.copyOf(freeto,F); target=Arrays.copyOf(target,T);
        //for (int[] a:new int[][] {freeto,tofree,target}) System.out.println(Arrays.toString(a));
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                        Rf[r]||Cf[c]?
                                ((S1[0][r]||S1[1][c]?"":"'")+tofree[r*C+c]):
                                "X"
                        //': piece that this BFS tree tries to solve; *: gripped piece
                );
            System.out.println();
        }
        {
            long tmp=1;
            for (int rep=0; rep<T; rep++) tmp*=F-rep;
            if (tmp>400_000_000) throw new RuntimeException("Too many combinations to handle.");
            ncombos=(int)tmp;
        }
        System.out.println("ncombos="+ncombos);

        //moves: every move is represented with [t,a,r]:
        //t: type (0=row shift, 1=clm shift)
        //a: the a-th (row if t==0, else clm)
        //r: # units to shift (right if t==0, else down)
        mvs=new int[2*R*C][]; mvactions=new int[2*R*C][]; {
            M=0;
            for (int mr=0; mr<R; mr++) if (Rf[mr])
                for (int s=-1; s<=1; s+=2) {
                    mvs[M]=new int[] {0,mr,s};
                    mvactions[M]=new int[F];
                    for (int i=0; i<F; i++) {
                        int r=freeto[i]/C, c=freeto[i]%C;
                        mvactions[M][i]=tofree[r*C+(r==mr?mod(c+s,C):c)];
                    }
                    M++;
                }
            for (int mc=0; mc<C; mc++) if (Cf[mc])
                for (int s=-1; s<=1; s+=2) {
                    mvs[M]=new int[] {1,mc,s};
                    mvactions[M]=new int[F];
                    for (int i=0; i<F; i++) {
                        int r=freeto[i]/C, c=freeto[i]%C;
                        mvactions[M][i]=tofree[(c==mc?mod(r+s,R):r)*C+c];
                    }
                    M++;
                }
            mvs=Arrays.copyOf(mvs,M);
            mvactions=Arrays.copyOf(mvactions,M);
        }
        mvreduc=new int[M+1][];
        for (int m=0; m<M; m++) {
            mvreduc[m]=new int[M];
            int sz=0;
            for (int mb=0; mb<M; mb++) if (mvokay(m,mb)) mvreduc[m][sz++]=mb;
            mvreduc[m]=Arrays.copyOf(mvreduc[m],sz);
        }
        mvreduc[M]=new int[M]; for (int m=0; m<M; m++) mvreduc[M][m]=m;
        String form="%-4s%-8s%s%n"; System.out.printf(form,"idx","move","idxs of moves allowed to come afterward");
        for (int m=0; m<=M; m++) System.out.printf(form,m,m<M?mvseqStr(Arrays.asList(mvs[m])):"-",Arrays.toString(mvreduc[m]));
        //BFS
        long st=System.currentTimeMillis();
        data=new long[ncombos]; Arrays.fill(data,-1);
        fronts=new ArrayList<>();
        {
            int[] solvedscrm=new int[T];
            for (int i=0; i<T; i++)
                solvedscrm[i]=tofree[target[i]];
            int solvedscrmcode=encode(solvedscrm);
            fronts.add(new int[] {solvedscrmcode});
            data[solvedscrmcode]=0;
        }
        int[] nfront=new int[ncombos];
        int reached=0;
        for (diam=0;; diam++) {
            reached+=fronts.get(diam).length;
            System.out.print((diam>0?" ":"")+diam+":"+fronts.get(diam).length);
            int sz=0;
            for (int f:fronts.get(diam)) {
                int[] scrm=decode(f);
                int[] mvlist=mvreduc[diam==0?M:mvi(f)];
                for (int mi:mvlist) {
                    int nf=encode(scrm,mvactions[mi]);
                    if (data[nf]==-1) {
                        data[nf]=compressed(diam+1,f,mi);
                        nfront[sz++]=nf;
                    }
                }
            }
            if (sz==0) break;
            fronts.add(Arrays.copyOf(nfront,sz));
        }
        System.out.println("\n#reached="+reached);
        System.out.println("diam="+diam);
        System.out.println("total BFS time="+(System.currentTimeMillis()-st));
    }
    /*
    encoding ordered combinations
    A[0]...A[K-1], 0<=A[i]<N, all A[i] distinct
    possible to transform permutation [0...N-1] into [....|A]
    using a sequence of swaps (i,J_i) for i=N-1 to N-K inclusive
      --> encode A as J_(N-1)+N*(J_(N-2)+(N-1)*(...+(N-K+2)*J_(N-K)...)
    for this program, N=Nfree, K=K
    */
    public int encode(int[] A) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-T; i--) {
            //swap idxs i and L[A[i-(N-K)]] in P
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
    public int encode(int[] A, int[] f) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-T; i--) {
            int j=L[f[A[i-(F-T)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    public int[] decode(int code) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        for (int v=F; v>F-T; v--) {
            int i=v-1, j=code%v;
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[T];
        System.arraycopy(P,F-T,out,0,T);
        return out;
    }
    public int[] toabsaction(int[] faction) {
        //faction[i]=j means the i-th free loc goes to the j-th free loc
        int[] out=new int[R*C];
        for (int l=0; l<R*C; l++)
            out[l]=tofree[l]==-1?l:(freeto[faction[tofree[l]]]);
        return out;
    }
    public int[] scrmaction(int code) {
        if (data[code]==-1) throw new RuntimeException("Invalid combination code: "+code);
        int[] ret=new int[F];
        for (int i=0; i<F; i++) ret[i]=i;
        for (int c=code; depth(c)>0; c=par(c))
            ret=prod(ret,mvactions[mvi(c)]);
        return toabsaction(ret);
    }
    public List<int[]> solvemvs(int code) {
        List<int[]> out=new ArrayList<>();
        for (int c=code; depth(c)>0; c=par(c)) {
            int[] mv=mvs[mvi(c)];
            out.add(new int[] {mv[0],mv[1],-mv[2]});
        }
        return out;
    }
    public static void main(String[] args) {
        new BFS("00011x00011","00001x00001");
    }
}
