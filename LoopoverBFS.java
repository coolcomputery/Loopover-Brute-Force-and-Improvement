import java.util.*;
public class LoopoverBFS {
    //TODO: REFACTOR USING ABSTRACT CLASS
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
    private static boolean free(boolean[][] boardState, int r, int c) {
        return boardState[0][r]||boardState[1][c];
    }
    //define absolute indexing as mapping coordinate (r,c) to index r*C+c
    //every scramble is represented by an array L[], where piece i is at location L[i]
    private int R, C;
    private int F;
    private boolean[][] rcfree;
    //a location (r,c) is free iff Rfree[r]||Cfree[c]
    private int[] tofree, freeto;
    //tofree[r*C+c]=i, where free location (r,c) is assigned to index i
    public int K;
    public int[] target; //list of pieces this tree tries to solve, in absolute indexing
    private int[][] mvactions, mvs;
    private int[][] solveactions, scrambleactions;
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
    private List<int[]> fronts; //BFS fronts
    public int D; //(largest depth of BFS tree)+1
    //c-->(depth,move from parent combo to c,parent combo)
    public int[] tofree() {
        return tofree;
    }
    public int[] freeto() {
        return freeto;
    }
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
    public LoopoverBFS(int R, int C, String state0, String state1) {
        long st=System.currentTimeMillis();
        this.R=R; this.C=C;
        rcfree=parseState(state0);
        tofree=new int[R*C]; freeto=new int[R*C];
        F=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if (free(rcfree,r,c)) {
                    tofree[r*C+c]=F;
                    freeto[F]=r*C+c;
                    F++;
                }
                else tofree[r*C+c]=-1;
        freeto=Arrays.copyOfRange(freeto,0, F);
        boolean[][] nrcfree=parseState(state1);
        K=0; target =new int[R*C];
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if (free(rcfree,r,c)&&!free(nrcfree,r,c))
                    target[K++]=r*C+c;
        target =Arrays.copyOfRange(target,0,K);
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                        free(rcfree,r,c)?
                                ((free(nrcfree,r,c)?"":"'")+tofree[r*C+c]):
                                "X"
                        //': piece that this BFS tree tries to solve; *: gripped piece
                );
            System.out.println();
        }
        {
            long tmp=1;
            for (int rep=0; rep<K; rep++) tmp*=F-rep;
            if (tmp>400_000_000) throw new RuntimeException("Too many combinations to handle.");
            ncombos=(int)tmp;
        }
        System.out.println("ncombos="+ncombos);

        //moves: every move is represented with [t,a,r]:
        //t: type (0=row shift, 1=clm shift)
        //a: the a-th (row if t==0, else clm)
        //r: # units to shift (right if t==0, else down)
        M=0;
        for (boolean[] axis:rcfree)
            for (boolean b:axis) if (b) M+=2;
        mvactions=new int[M][]; mvs=new int[M][]; {
            //mvactions[m][i]=free loc. that i-th free loc. will go to after move m is applied
            int idx=0;
            for (int mr=0; mr<R; mr++)
                if (rcfree[0][mr])
                    for (int s=-1; s<=1; s+=2) {
                        mvs[idx]=new int[] {0,mr,s};
                        mvactions[idx]=new int[F];
                        for (int i=0; i<F; i++) {
                            int r=freeto[i]/C, c=freeto[i]%C;
                            mvactions[idx][i]=tofree[r*C+(r==mr?mod(c+s,C):c)];
                        }
                        idx++;
                    }
            for (int mc=0; mc<C; mc++)
                if (rcfree[1][mc])
                    for (int s=-1; s<=1; s+=2) {
                        mvs[idx]=new int[] {1,mc,s};
                        mvactions[idx]=new int[F];
                        for (int i=0; i<F; i++) {
                            int r=freeto[i]/C, c=freeto[i]%C;
                            mvactions[idx][i]=tofree[(c==mc?mod(r+s,R):r)*C+c];
                        }
                        idx++;
                    }
        }
        int[][] mvreduc=mvreduc(mvs);
        //BFS
        solveactions=new int[ncombos][];
        scrambleactions=new int[ncombos][];
        data=new long[ncombos]; Arrays.fill(data,-1);
        fronts=new ArrayList<>();
        {
            int[] solvedscrm=new int[K];
            for (int i=0; i<K; i++)
                solvedscrm[i]=tofree[target[i]];
            int solvedscrmcode=comboCode(solvedscrm);
            fronts.add(new int[] {solvedscrmcode});
            data[solvedscrmcode]=0;
        }
        int[] nfront=new int[ncombos];
        int reached=0;
        for (D=0;; D++) {
            if (fronts.get(D).length==0) break;
            reached+=fronts.get(D).length;
            System.out.print((D>0?" ":"")+D+":"+fronts.get(D).length);
            int sz=0;
            for (int f:fronts.get(D)) {
                int[] scrm=codeCombo(f);
                int[] mvlist=mvreduc[D==0?M:mvi(f)];
                for (int mi:mvlist) {
                    int nf=comboCode(scrm,mvactions[mi]);
                    if (data[nf]==-1) {
                        data[nf]=compressed(D+1,f,mi);
                        nfront[sz++]=nf;
                    }
                }
            }
            fronts.add(new int[sz]);
            System.arraycopy(nfront,0,fronts.get(D+1),0,sz);
        }
        System.out.println("\n#reached="+reached);
        System.out.println("D="+D);
        System.out.println("total BFS time="+(System.currentTimeMillis()-st));
    }
    public void clearFronts() {
        fronts=null;
    }
    public int[] codesAtDepth(int d) {
        return fronts.get(d);
    }
    /*
    encoding ordered combinations
    A[0]...A[K-1], 0<=A[i]<N, all A[i] distinct
    possible to transform permutation [0...N-1] into [....|A]
    using a sequence of swaps (i,J_i) for i=N-1 to N-K inclusive
      --> encode A as J_(N-1)+N*(J_(N-2)+(N-1)*(...+(N-K+2)*J_(N-K)...)
    for this program, N=Nfree, K=K
    */
    public int comboCode(int[] A) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-K; i--) {
            //swap idxs i and L[A[i-(N-K)]] in P
            int j=L[A[i-(F-K)]];
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
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-K; i--) {
            int j=L[f[A[i-(F-K)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    public int codeAfterScramble(int[] scrm0) {
        //A[i]=tofree[scrm0[scrm1[target[i]]]]
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-K; i--) {
            int j=L[tofree[scrm0[target[i-(F-K)]]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    public int codeAfterScramble(int[] scrm0, int[] scrm1) {
        //A[i]=tofree[scrm0[scrm1[target[i]]]]
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-K; i--) {
            int j=L[tofree[scrm0[scrm1[target[i-(F-K)]]]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    public int codeAfterScramble(int[] scrm0, int[] scrm1, int[] scrm2) {
        //A[i]=tofree[scrm0[scrm1[scrm2[target[i]]]]]
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-K; i--) {
            int j=L[tofree[scrm0[scrm1[scrm2[target[i-(F-K)]]]]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    public int[] codeCombo(int code) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        for (int v=F; v> F-K; v--) {
            int i=v-1, j=code%v;
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[K];
        System.arraycopy(P, F-K,out,0,K);
        return out;
    }
    public void computeAllActions() {
        for (int code=0; code<ncombos; code++) if (data[code]!=-1) {
            solveactions[code]=solveaction_help(code);
            scrambleactions[code]=inv(solveactions[code]);
        }
    }
    public int[] solveaction(int code) {
        return solveactions[code]==null?solveaction_help(code):solveactions[code];
    }
    private int[] solveaction_help(int code) {
        if (data[code]==-1) throw new RuntimeException("Invalid combination code: "+code);
        int[] out=new int[F];
        for (int i=0; i<F; i++) out[i]=i;
        for (int c=code; depth(c)>0; c=par(c)) {
            int[] mva=inv(mvactions[mvi(c)]);
            int[] nout=new int[F];
            for (int i=0; i<F; i++)
                nout[i]=mva[out[i]];
            out=nout;
        }
        return mva2abs(out);
    }
    public int[] scrambleaction(int code) {
        return scrambleactions[code]==null?inv(solveaction(code)):scrambleactions[code];
    }
    public List<int[]> solvemvs(int code) {
        List<int[]> out=new ArrayList<>();
        for (int c=code; depth(c)>0; c=par(c)) {
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
