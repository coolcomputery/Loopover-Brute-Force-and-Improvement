import java.util.*;
public class LoopoverBFS {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    //every scramble is represented by an array L[], where piece i is at location L[i]
    private int R, C;
    private int Nfree;
    private boolean[] Rfree, Cfree;
    //a location (r,c) is free iff Rfree[r]||Cfree[c]
    private int[] tofree, freeto;
    //tofree[r*C+c]=i, where free location (r,c) is assigned to index i
    private int K;
    private int[] solvedscramble;
    private int[][] mvactions, mvs;
    private int M;
    private int ncombos;
    //bfs stuff
    private long[] data;
    //c-->(depth,parent combo,move from parent combo to c)
    //  --> (depth*ncombos+(parent combo))*mvs.length+(move)
    private long compressed(int depth, int parent, int move) {
        return ((long)depth*ncombos+parent)*M+move;
    }
    public LoopoverBFS(int R, int C, String rf0, String cf0, String rs1, String cs1) {
        this.R=R; this.C=C;
        Rfree=new boolean[R]; Cfree=new boolean[C];
        for (int i=0; i<R; i++)
            Rfree[i]=rf0.charAt(i)=='1';
        for (int i=0; i<C; i++)
            Cfree[i]=cf0.charAt(i)=='1';
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
        boolean[] Rnfree=new boolean[R], Cnfree=new boolean[C];
        for (int i=0; i<R; i++)
            Rnfree[i]=rs1.charAt(i)=='1';
        for (int i=0; i<C; i++)
            Cnfree[i]=cs1.charAt(i)=='1';
        K=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    K++;
        solvedscramble=new int[K];
        for (int r=0, idx=0; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    solvedscramble[idx++]=tofree[r*C+c];
        System.out.println(Arrays.toString(solvedscramble));
        {
            long tmp=1;
            for (int rep=0; rep<K; rep++) tmp*=Nfree-rep;
            if (tmp>400_000_000) throw new RuntimeException("Too many combinations to handle.");
            ncombos=(int)tmp;
        }
        System.out.println("ncombos="+ncombos);
        //moves: shifting row r right/left one unit, clm c down/up one unit
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
        //every move is represented with [t,a,r]:
        //t: type (0=row shift, 1=clm shift)
        //a: the a-th (row if t==0, else clm)
        //r: # units to shift (right if t==0, else down)
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
        //BFS
        data=new long[ncombos]; Arrays.fill(data,-1);
        int[] bfsList=new int[ncombos]; int fsz=0;
        bfsList[fsz++]=comboCode(solvedscramble);
        data[bfsList[0]]=0;
        for (int depth=0, fi=0; fi<fsz; depth++) {
            System.out.println(depth+":"+(fsz-fi));
            for (int sz=fsz; fi<sz; fi++) {
                int f=bfsList[fi];
                int[] scrm=codeCombo(f);
                int[] mvlist=mvreduc[fi>0?(int)(data[f]%M):M];
                for (int mi:mvlist) {
                    int nf=mvcomboCode(scrm,mi);
                    if (data[nf]==-1) {
                        data[nf]=compressed(depth+1,f,mi);
                        bfsList[fsz++]=nf;
                    }
                }
            }
        }
        System.out.println("#reached="+fsz);
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
    private int mvcomboCode(int[] A, int mi) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=Nfree-1, pow=1; i>=Nfree-K; i--) {
            //swap idxs i and L[A[i-(N-K)]] in P
            int j=L[mvactions[mi][A[i-(Nfree-K)]]];
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
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        new LoopoverBFS(5,5
                ,"11111","11111"
                ,"00111","00011"
                //,"00011","00001"
        );
        /*new LoopoverBFS(5,5
                ,"00111","00011"
                ,"00011","00001"
        );*/
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
