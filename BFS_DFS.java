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
    private static int[] inv(int[] P) {
        int[] iP=new int[P.length];
        for (int i=0; i<P.length; i++) iP[P[i]]=i;
        return iP;
    }
    private static class MapL2B { //map long --> byte
        //TODO: TRIE?
        int size;
        int B;
        int[][] bins; byte[][] vals; int[] binSizes;
        public MapL2B(long U, int B) {
            size=0;
            this.B=B;
            bins=new int[(int)(U/B)+1][]; vals=new byte[bins.length][];
            binSizes=new int[bins.length];
            System.out.printf("U=%d B=%d # bins=%d%n",U,B,bins.length);
        }
        public void put(long k, byte v) {
            //this program is guaranteed to call put(k,v) only if the map does not already contain k
            int b=(int)(k/B);
            if (bins[b]==null) {
                bins[b]=new int[1]; vals[b]=new byte[1];
            }
            if (binSizes[b]==bins[b].length) {
                bins[b]=Arrays.copyOf(bins[b],2*bins[b].length);
                vals[b]=Arrays.copyOf(vals[b],2*vals[b].length);
            }
            bins[b][binSizes[b]]=(int)(k%B); vals[b][binSizes[b]]=v;
            binSizes[b]++;

            size++;
        }
        public byte get(long k) {
            int b=(int)(k/B), r=(int)(k%B);
            for (int i=0; i<binSizes[b]; i++) if (bins[b][i]==r) return vals[b][i];
            throw new RuntimeException();
        }
        public boolean containsKey(long k) {
            int b=(int)(k/B), r=(int)(k%B);
            for (int i=0; i<binSizes[b]; i++) if (bins[b][i]==r) return true;
            return false;
        }
        public int size() {
            return size;
        }
    }

    private int R, C;
    private boolean[] Rf, Cf;
    private int F,T,M;
    private int[] f2a, a2f; public int[] target;
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
    private MapL2B mvi;
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
        long[] front={encode(prod(a2f,target))};
        mvi=new MapL2B(ncombos,(int)(ncombos/50_000_000)+1); {
            long s=front[0];
            mvi.put(s,(byte)M);
        }
        System.out.println("0:"+front.length);
        for (int D=1; D<=LIM; D++) {
            long[] nfront=new long[1];
            int nfsz=0;
            for (long f:front) {
                int[] scrm=decode(f);
                for (int mi:mvreduc[mvi.get(f)]) {
                    long nf=encode(prod(mvfactions[mi],scrm));
                    if (!mvi.containsKey(nf)) {
                        mvi.put(nf,(byte)mi);
                        if (nfsz==nfront.length) nfront=Arrays.copyOf(nfront,2*nfront.length);
                        nfront[nfsz++]=nf;
                    }
                }
            }
            front=Arrays.copyOf(nfront,nfsz);
            System.out.println(D+":"+front.length);
        }
        System.out.println("# perms at depth<="+LIM+"="+mvi.size());
        System.out.println("bfs time="+(System.currentTimeMillis()-st));
    }
    public long nfound() {
        return mvi.size();
    }
    private long par(long c) {
        return encode(prod(inv(mvfactions[mvi.get(c)]),decode(c)));
    }
    private List<int[]> solmoves(long c0) {
        List<int[]> out=new ArrayList<>();
        for (long c=c0; mvi.get(c)!=M; c=par(c)) {
            int mi=mvi.get(c);
            int[] mvn=mvnames[mi];
            out.add(new int[] {mvn[0],mvn[1],-mvn[2]});
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
        solved=false;
        mvseq=new int[search_lim+1][];
        sol=null; nnodes=0; nattempts=0;
        long st=System.currentTimeMillis();
        for (lim=0; !solved && lim<=search_lim; lim++) {
            System.out.println("lim="+lim+" time="+(System.currentTimeMillis()-st));
            dfs(fregion,0,M);
        }
        return sol;
    }
    private int lim;
    private boolean solved;
    public long nnodes, nattempts;
    private int[][] mvseq;
    private List<int[]> sol;
    private void dfs(int[] fscrm, int nmvs, int prevmi) {
        if (solved) return;
        nnodes++;
        if (nmvs==lim) {
            nattempts++;
            long code=encode(fscrm);
            if (mvi.containsKey(code)) {
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

    private static void printBoard(int R, int C, int[] scrm) {
        int[] board=new int[R*C]; Arrays.fill(board,-1);
        for (int i=0; i<R*C; i++) if (scrm[i]!=-1) board[scrm[i]]=i;
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++) {
                int v=board[r*C+c];
                if (R*C<=26) System.out.print(v==-1?".":(char)(v+'A'));
                else System.out.printf("%3s",v==-1?".":v);
            }
            System.out.println();
        }
    }
    public static int[] partialBoard(int R, int C, int[] pieces, int[] locations) {
        int[] scrm=new int[R*C]; Arrays.fill(scrm,-1);
        for (int i=0; i<pieces.length; i++) scrm[pieces[i]]=locations[i];
        return scrm;
    }
    public static void main(String[] args) {
        Object[][] tests={{"11111x11111","00011x00011",8,new int[] {24,23,22,19,18,17,14,13,12}},
                {"00011x00011","00000x00000",11,new int[] {15,20, 16,21, 17,22, 3,8,13,18,23, 4,9,14,19,24}}};
        for (Object[] test:tests) {
            BFS_DFS t=new BFS_DFS((String)test[0],(String)test[1],(int)test[2]);
            int[] scrm=(int[])test[3];
            printBoard(t.R,t.C,partialBoard(t.R,t.C,t.target,scrm));
            long st=System.currentTimeMillis();
            List<int[]> sol=t.sol(scrm,20);
            System.out.println("dfs time="+(System.currentTimeMillis()-st));
            System.out.println(mvseqStr(sol));
        }
    }
}
