import java.util.*;
/**
 * Constructs entire BFS tree of expanding solved region S0 to S1.
 */
public class BFS {
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
    public int R, C, F;
    private boolean[] Rf, Cf; //cell (r,c) is free iff Rf[r]||Cf[c]
    public int[] preblock;
    public int[] a2f, f2a; //for cell (r,c), a=r*C+c: a2f[a]=f if a is the f-th free location, else -1; f2a[f]=a
    //a is in "absolute coordinates", f is in "free coordinates"
    public int T;
    public int[] target; //list of pieces this tree tries to solve, in absolute coordinates
    /*
    encoding ordered combinations
    A[0]...A[T-1], 0<=A[i]<F, all A[i] distinct
    possible to transform permutation [0...F-1] into [....|A]
    using a sequence of swaps (i,J_i) for i=F-1 to F-T inclusive
      --> encode A as J_(F-1)+F*(J_(F-2)+(F-1)*(...+(F-T+2)*J_(F-T)...)
    */
    public int encode(int[] A) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-T; i--) {
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
    public int encodeprod(int[] A, int[] B) { //computes encode(prod(A,B))
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-T; i--) {
            int j=L[A[B[i-(F-T)]]];
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
        return Arrays.copyOfRange(P,F-T,F);
    }

    public int M;
    public int[][] mvfactions, mvnames, mvreduc;

    //bfs stuff
    public int ncombos;
    public byte[] depth, mvi; private int[] par;
    public List<int[]> fronts; //BFS fronts
    public int diam; //depth of BFS tree
    public BFS(String state0, String state1) {
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
        //for (int[] a:new int[][] {freeto,tofree,target}) System.out.println(Arrays.toString(a));
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                        Rf[r]||Cf[c]?
                                ((S1[0][r]||S1[1][c]?"":"'")+ a2f[r*C+c]):
                                "X"
                        //': piece that this BFS tree tries to solve; *: gripped piece
                );
            System.out.println();
        }
        System.out.printf("f2a=%s%na2f%s%ntarget=%s%n",Arrays.toString(f2a),Arrays.toString(a2f),Arrays.toString(target));
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
        mvnames=new int[2*R*C][]; mvfactions=new int[2*R*C][]; {
            M=0;
            for (int t=0; t<2; t++)
                for (int co=0; co<(t==0?R:C); co++) if ((t==0?Rf:Cf)[co])
                    for (int s=-1; s<=1; s+=2) {
                        mvnames[M]=new int[] {t,co,s};
                        mvfactions[M]=new int[F];
                        for (int f=0; f<F; f++) {
                            int r=f2a[f]/C, c=f2a[f]%C;
                            mvfactions[M][f]= a2f[t==0?(r*C+(r==co?mod(c+s,C):c)):(c==co?mod(r+s,R):r)*C+c];
                        }
                        M++;
                    }
            mvnames=Arrays.copyOf(mvnames,M);
            mvfactions=Arrays.copyOf(mvfactions,M);
            if (M>Byte.MAX_VALUE) throw new RuntimeException("M="+M+">Byte.MAX_VALUE="+Byte.MAX_VALUE);
        }
        mvreduc=new int[M+1][];
        for (int m=0; m<M; m++) {
            mvreduc[m]=new int[M]; int sz=0;
            for (int mb=0; mb<M; mb++) {
                int[] mva=mvnames[m], mvb=mvnames[mb];
                if (mva[0]!=mvb[0]||mva[1]<mvb[1]||(mva[1]==mvb[1]&&mva[2]+mvb[2]!=0))
                    mvreduc[m][sz++]=mb;
            }
            mvreduc[m]=Arrays.copyOf(mvreduc[m],sz);
        }
        mvreduc[M]=new int[M]; for (int m=0; m<M; m++) mvreduc[M][m]=m;
        //String form="%-4s%-8s%s%n"; System.out.printf(form,"idx","move","idxs of moves allowed to come afterward");
        //for (int m=0; m<=M; m++) System.out.printf(form,m,m<M?mvnameStr(mvnames[m]):"-",Arrays.toString(mvreduc[m]));
        //BFS
        long st=System.currentTimeMillis();
        depth=new byte[ncombos]; mvi=new byte[ncombos]; par=new int[ncombos];
        Arrays.fill(depth,(byte)(-2)); Arrays.fill(mvi,(byte)(-2)); Arrays.fill(par,-2);
        fronts=new ArrayList<>();
        {
            int solvedscrmcode=encode(prod(a2f,target));
            fronts.add(new int[] {solvedscrmcode});
            depth[solvedscrmcode]=0; mvi[solvedscrmcode]=(byte)M; par[solvedscrmcode]=-1;
        }
        int[] nfront=new int[ncombos];
        int reached=0;
        for (diam=0;; diam++) {
            if (diam>Byte.MAX_VALUE) throw new RuntimeException("diam="+diam+">Byte.MAX_VALUE="+Byte.MAX_VALUE);
            reached+=fronts.get(diam).length;
            System.out.print((diam>0?" ":"")+diam+":"+fronts.get(diam).length);
            int sz=0;
            for (int f:fronts.get(diam)) {
                int[] scrm=decode(f);
                int[] mvlist=mvreduc[mvi[f]];
                for (int mi:mvlist) {
                    int nf=encodeprod(mvfactions[mi],scrm);
                    if (depth[nf]==-2) {
                        depth[nf]=(byte)(diam+1);
                        par[nf]=f;
                        mvi[nf]=(byte)mi;
                        nfront[sz++]=nf;
                    }
                }
            }
            if (sz==0) break;
            fronts.add(Arrays.copyOf(nfront,sz));
        }
        System.out.println("\n#reached="+reached+"\ndiam="+diam+"\ntotal BFS time="+(System.currentTimeMillis()-st));
    }
    public int[] toabsaction(int[] faction) { //faction[i]=j means the i-th free loc goes to the j-th free loc
        int[] out=new int[R*C];
        for (int l=0; l<R*C; l++)
            out[l]=a2f[l]==-1?l:(f2a[faction[a2f[l]]]);
        return out;
    }
    public int[] scrmaction(int code) {
        if (depth[code]<0) throw new RuntimeException("Invalid combination code: "+code);
        int[] ret=new int[F];
        for (int i=0; i<F; i++) ret[i]=i;
        for (int c=code; depth[c]>0; c=par[c])
            ret=prod(ret,mvfactions[mvi[c]]);
        return toabsaction(ret);
    }
    public List<int[]> solvemvs(int code) {
        List<int[]> out=new ArrayList<>();
        for (int c=code; depth[c]>0; c=par[c]) {
            int[] mv=mvnames[mvi[c]];
            out.add(new int[] {mv[0],mv[1],-mv[2]});
        }
        return out;
    }
}
