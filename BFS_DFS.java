import java.util.*;
public class BFS_DFS {
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
    private static String mvnameStr(int[] mvname) {
        return (mvname[0]==0?"R":"C")+mvname[1]+(mvname[2]==-1?"'":mvname[2]==1?"":("^"+mvname[2]));
    }
    public static String mvseqStr(List<int[]> S) {
        StringBuilder str=new StringBuilder();
        for (int[] mvn:S)
            str.append(" ").append(mvnameStr(mvn));
        return str.substring(Math.min(str.length(),1));
    }
    private static int[] prod(int[] A, int[] B) {//return [ A[B[i]] for all i ]
        int[] out=new int[B.length];
        for (int i=0; i<B.length; i++) out[i]=A[B[i]];
        return out;
    }

    private int R, C;
    private boolean[] Rf, Cf;
    private int F,T,M;
    private int[] f2a, a2f; public int[] target;
    private long bfsSize;
    public long encode(int[] A) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i=F-1; i>=F-T; i--) {
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
    public int[] decode(long code) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        for (int v=F; v>F-T; v--) {
            int i=v-1, j=(int)(code%v);
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[T];
        System.arraycopy(P,F-T,out,0,T);
        return out;
    }

    private long ncombos;
    private int[][] mvnames, mvfactions, mvreduc;
    List<long[]> fronts;
    private boolean mvokay(int mai, int mbi) {
        int[] mva=mvnames[mai], mvb=mvnames[mbi];
        return mva[0]!=mvb[0]||mva[1]<mvb[1]
                ||(mva[1]==mvb[1]&&mva[2]+mvb[2]!=0);
    }
    public BFS_DFS(String sS0, String sS1, int LIM) {
        boolean[][] S0=parseState(sS0), S1=parseState(sS1);
        Rf=S0[0]; Cf=S0[1];
        R=Rf.length; C=Cf.length;
        F=0; f2a=new int[R*C]; a2f=new int[R*C]; Arrays.fill(a2f,-1);
        T=0; target=new int[R*C];
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (Rf[r]||Cf[c]) {
            int l=r*C+c;
            a2f[l]=F; f2a[F]=l;
            if (!S1[0][r]&&!S1[1][c]) target[T++]=l;
            F++;
        }
        f2a=Arrays.copyOfRange(f2a,0,F); target=Arrays.copyOfRange(target,0,T);
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
        ncombos=1;
        for (int rep=0; rep<T; rep++) ncombos*=F-rep;
        System.out.println("ncombos="+ncombos);

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
            mvreduc[m]=new int[M];
            int sz=0;
            for (int mb=0; mb<M; mb++) if (mvokay(m,mb)) mvreduc[m][sz++]=mb;
            mvreduc[m]=Arrays.copyOf(mvreduc[m],sz);
        }
        mvreduc[M]=new int[M]; for (int m=0; m<M; m++) mvreduc[M][m]=m;

        //partial BFS
        System.out.println("partial BFS");
        long st=System.currentTimeMillis();
        fronts=new ArrayList<>(Collections.singletonList(new long[] {encode(prod(a2f,target))}));
        System.out.println("0:"+fronts.get(0).length);
        for (int D=1; D<=LIM; D++) {
            long[] nfront=new long[1];
            int nfsz=0;
            for (long f:fronts.get(D-1)) {
                int[] scrm=decode(f);
                for (int mi=0; mi<M; mi++) {
                    long nf=encode(prod(mvfactions[mi],scrm));
                    if (Arrays.binarySearch(fronts.get(D-1),nf)<0 && (D==1 || Arrays.binarySearch(fronts.get(D-2),nf)<0)) {
                        if (nfsz==nfront.length) nfront=Arrays.copyOf(nfront,2*nfront.length);
                        nfront[nfsz++]=nf;
                    }
                }
            }
            Arrays.sort(nfront,0,nfsz);
            int cnt=0;
            for (int i=0; i<nfsz; i++)
                if (i==0 || nfront[i]>nfront[i-1]) nfront[cnt++]=nfront[i];
            fronts.add(Arrays.copyOf(nfront,cnt));
            System.out.println(D+":"+cnt);
        }
        bfsSize=0;
        for (long[] front:fronts) bfsSize+=front.length;
        System.out.println("# perms at depth<="+LIM+"="+bfsSize);
        System.out.println("bfs time="+(System.currentTimeMillis()-st));

        lastFront=fronts.get(fronts.size()-1);
        Arrays.sort(lastFront);
        int maxJumps=500_000_000;
        if (ncombos>Integer.MAX_VALUE*(long)maxJumps) throw new RuntimeException("ncombos="+ncombos+">2^30 * "+maxJumps);
        blockWidth=(int)(ncombos/maxJumps)+1;
        System.out.println("blockWidth="+blockWidth);
        blockL=new int[(int)(ncombos/blockWidth)+2]; Arrays.fill(blockL,lastFront.length);
        blockR=new int[blockL.length]; Arrays.fill(blockR,-1);
        //blockL[b]=lowest i s.t. lastFront[i]/blockWidth=b
        //blockR[b]=highest i s.t. //
        for (int i=0; i<lastFront.length; i++) {
            long v=lastFront[i];
            int b=(int)(v/blockWidth);
            blockL[b]=Math.min(blockL[b],i);
            blockR[b]=Math.max(blockR[b],i);
        }
    }
    public long nfound() {
        return bfsSize;
    }
    private List<int[]> solmoves(long c) {
        List<int[]> out=new ArrayList<>();
        int depth=-1;
        for (int d=0; d<fronts.size(); d++)
            if (Arrays.binarySearch(fronts.get(d),c)>=0) {
                depth=d;
                break;
            }
        if (depth==-1) return null;
        for (int d=depth; d>0; d--) {
            int[] p=decode(c);
            for (int mi=0; mi<M; mi++) {
                long nc=encode(prod(mvfactions[mi],p));
                if (Arrays.binarySearch(fronts.get(d-1),nc)>=0) {
                    c=nc;
                    out.add(mvnames[mi]);
                    break;
                }
            }
        }
        return out;
    }
    public List<int[]> sol(int[] region, int search_lim) { //region[t]=absolute location that t-th target piece is at
        int[] fregion=prod(a2f,region);
        {
            boolean[] exists=new boolean[F];
            for (int v:fregion)
                if (v<0||v>=F||exists[v]) throw new RuntimeException("Invalid scramble:"+Arrays.toString(region));
                else exists[v]=true;
        }
        {
            List<int[]> out=solmoves(encode(fregion));
            if (out!=null) return out;
        }
        solved=false;
        mvseq=new int[search_lim+1][];
        sol=null; nnodes=0; nattempts=0; searchWork=0;
        for (lim=0; !solved && lim<=search_lim; lim++)
            dfs(fregion,0,M);
        return sol;
    }
    private long[] lastFront;
    private int[] blockL, blockR; private int blockWidth;
    private boolean inLastFront(long c) {
        int b=(int)(c/blockWidth);
        int lo=blockL[b], hi=blockR[b];
        while (lo<hi) {
            searchWork++;
            int mi=(lo+hi)/2;
            if (lastFront[mi]>=c) hi=mi;
            else lo=mi+1;
        }
        return lo<lastFront.length && lastFront[lo]==c;
    }
    private int lim;
    private boolean solved;
    public long nnodes, nattempts, searchWork;
    private int[][] mvseq;
    private List<int[]> sol;
    private void dfs(int[] fscrm, int nmvs, int prevmi) {
        if (solved) return;
        nnodes++;
        if (nmvs==lim) {
            nattempts++;
            long code=encode(fscrm);
            //let L be the furthest distance our preprocessed BFS went out to
            //if fscrm can be solved in <=L moves,
            // we would have already found out by searching for it in the stored BFS fronts
            //otherwise, fscrm must take >L moves to solve,
            // so as we iteratively DFS over increasingly longer sequences to transform fscrm
            // into a scramble that is contained in the BFS fronts,
            // the first time this is done is when we are in the outermost front of BFS
            //therefore we only have to search in the outermost front
            if (inLastFront(code)) {
                solved=true;
                sol=new ArrayList<>();
                for (int i=0; i<nmvs; i++) sol.add(mvseq[i]);
                sol.addAll(solmoves(code));
            }
            return;
        }
        for (int mi:mvreduc[prevmi]) if (!solved) {
            int[] nfscrm=prod(mvfactions[mi],fscrm);
            if (!Arrays.equals(nfscrm,fscrm)) {
                mvseq[nmvs]=mvnames[mi];
                dfs(prod(mvfactions[mi],fscrm),nmvs+1,mi);
            }
        }
    }
}
