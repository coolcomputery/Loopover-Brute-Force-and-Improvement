import java.util.*;
import java.math.BigInteger;
public class LoopoverLowerBounds {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    /*
    Define >>r to be the action of shifting row r right 1 unit,
        and ,,c to be the action of shifting column c down 1 unit
    A horizontal syllable H shifts row r right H[r] units
        Thus, we can write H as PROD_r (>>r)^H[r]
    A vertical syllable V shifts column c down 1 unit
        We can write V as PROD_c (,,c)^V[c]
     */
    private static int[] sylAct(int R, int C, int[] S, int type) {
        int[] out=new int[R*C];
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                out[r*C+c]=type==0?(r*C+mod(c+S[r],C)):(mod(r+S[c],R)*C+c);
        return out;
    }
    private static int[] comp(int[] A, int[] B) {
        int[] out=new int[A.length];
        for (int i=0; i<A.length; i++)
            out[i]=B[A[i]];
        return out;
    }
    private static List<int[]> binnedSyllables(int R, int C) {
        //time complexity: O(R^C)
        List<int[]> syllables=new ArrayList<>();
        int[] S=new int[R]; S[0]=1;
        while (S[R-1]<C) {
            syllables.add(Arrays.copyOf(S,R));
            S[0]++;
            for (int i=0; i<R-1&&S[i]==C; i++) {
                S[i]=0;
                S[i+1]++;
            }
        }
        return syllables;
    }
    /*
    R1 C0 R0 C0' == C0 R0 C0' R1 on 5x5
    More generally, for some syllables ...H0 V0 H1 V1 H2...,
    Let S(V0,H0,V1)={r | (>>r) V0 H1 V1 == V0 H1 V0 (>>r)}
    we call the r in S(V0,H0,V1) the
    Then we can force horizontal syllable H2 to not shift any rows r s.t. r is in S
    Because if H2 did shift such rows, we could do the following:
    S=S(V0,H0,V1)
    H2=(PROD_{r in S}(>>r)^H2[k]) H2'
    --> H0 V0 H1 V1 H2  == H0 V0 H1 V1 (PROD_{r in S}(>>r)^H2[k]) H2'
                        == H0 (PROD_{r in S}(>>r)^H2[k]) V0 H1 V1 H2'
                        == H0' V0 H1 V1 H2',
    where H0'=H0 (PROD_{r in S}(>>r)^H2[k])

    Let M(A)={x|A[x]!=0} (works with horizontal/vertical syllables)
    The above requirement can be written as: S(V0,H0,V1)&M(H1)==empty
    everything written above also applies for V0 H0 V1 H1 V2 (i.e. if the types of all syllables are reversed)

    Because doing this for all possible syllable triplets V0 H1 V1 is impractical for 5x5 Loopover ((5^5)^3=~30 billion states),
        we only use this new reduction technique for syllable triplets inv(V) H V
    */
    private static int avoiding(int R, int C, int[] X, int[] Y, int[] Z, int type) {
        //if type==0: find all r s.t. (>>r)XYZ == XYZ(>>r)
        //if type==1: find all c s.t. (,,c)XYZ == XYZ(,,c)
        int[] act=comp(comp(sylAct(R,C,X,1-type),sylAct(R,C,Y,type)),sylAct(R,C,Z,1-type));
        int out=0;
        if (type==0) {
            for (int r=0; r<R; r++) {
                boolean avoid=true;
                for (int c=0; c<C&&avoid; c++) {
                    int act_shift=act[r*C+c];
                    if (act_shift/C==r) act_shift=act_shift/C*C+mod(act_shift%C+1,C);
                    int shift_act=act[r*C+mod(c+1,C)];
                    if (act_shift!=shift_act)
                        avoid=false;
                }
                if (avoid) out|=1<<r;
            }
        }
        else if (type==1) {
            for (int c=0; c<C; c++) {
                boolean avoid=true;
                for (int r=0; r<R&&avoid; r++) {
                    int act_shift=act[r*C+c];
                    if (act_shift%C==c) act_shift=mod(act_shift/C+1,R)*C+act_shift%C;
                    int shift_act=act[mod(r+1,C)*R+c];
                    if (act_shift!=shift_act)
                        avoid=false;
                }
                if (avoid) out|=1<<c;
            }
        }
        else throw new RuntimeException("type!=0,1");
        return out;
    }
    private static int moving(int R, int C, int[] S, int t) {
        int out=0;
        if (t==0) {
            for (int r=0; r<R; r++)
                if (S[r]!=0) out|=1<<r;
        }
        else {
            for (int c=0; c<C; c++)
                if (S[c]!=0) out|=1<<c;
        }
        return out;
    }
    private static int idx(int R, int C, int[] S, int type) {
        int out=0;
        if (type==0)
            for (int i=0, pow=1; i<R; i++, pow*=C)
                out+=S[i]*pow;
        else
            for (int i=0, pow=1; i<C; i++, pow*=R)
                out+=S[i]*pow;
        return out-1;
    }
    private static int cost(int R, int C, int[] S, int type) {
        int out=0;
        if (type==0)
            for (int i=0; i<R; i++)
                out+=Math.min(S[i],C-S[i]);
        else
            for (int i=0; i<C; i++)
                out+=Math.min(S[i],R-S[i]);
        return out;
    }
    private static int[] inv(int R, int C, int[] S, int type) {
        int[] out;
        if (type==0) {
            out=new int[R];
            for (int i=0; i<R; i++)
                out[i]=(C-S[i])%C;
        }
        else {
            out=new int[C];
            for (int i=0; i<C; i++)
                out[i]=(R-S[i])%R;
        }
        return out;
    }
    public static void main(String[] args) {
        long timest=System.currentTimeMillis();
        int R=5, C=5;
        //syllables(t,d)=List<int[]> of all syllables of type t
        List<List<int[]>> syls=new ArrayList<>(Arrays.asList(
                binnedSyllables(R,C),binnedSyllables(C,R)
        ));
        int[] nSyls=new int[2];
        for (int t=0; t<2; t++) nSyls[t]=syls.get(t).size();
        System.out.println("nSyls="+Arrays.toString(nSyls));
        int[][] invidx=new int[2][], movemask=new int[2][], sylcost=new int[2][];
        for (int t=0; t<2; t++) {
            invidx[t]=new int[nSyls[t]];
            movemask[t]=new int[nSyls[t]];
            sylcost[t]=new int[nSyls[t]];
            for (int[] B:syls.get(t)) {
                int bi=idx(R,C,B,t);
                invidx[t][bi]=idx(R,C,inv(R,C,B,t),t);
                movemask[t][bi]=moving(R,C,B,t);
                sylcost[t][bi]=cost(R,C,B,t);
            }
        }
        int[][] sylcnt=new int[2][];
        for (int t=0; t<2; t++) {
            sylcnt[t]=new int[1+(t==0?(R*(C/2)):(C*(R/2)))];
            for (int si=0; si<nSyls[t]; si++)
                sylcnt[t][sylcost[t][si]]++;
            for (int d=0; d<sylcnt[t].length; d++)
                System.out.print(" "+d+":"+sylcnt[t][d]);
            System.out.println();
        }
        //System.out.println(Arrays.toString(avoiding(5,5,new int[] {1,0,0,0,0},new int[] {1,0,0,0,0},new int[] {-1,0,0,0,0},0)));
        boolean[][][] avoidPreprocess=new boolean[2][][];
        int[][][] avoidmasks=new int[2][][];
        //avoidPreprocess(A,B)=S(inv(A),inv(B),A)&M(B)==empty
        for (int t=0; t<2; t++) {
            avoidPreprocess[t]=new boolean[nSyls[1-t]][nSyls[t]];
            avoidmasks[t]=new int[nSyls[1-t]][nSyls[t]];
            for (int[] A:syls.get(1-t)) {
                int ai=idx(R,C,A,1-t);
                int[] iA=inv(R,C,A,1-t);
                for (int[] B:syls.get(t)) {
                    int bi=idx(R,C,B,t);
                    avoidmasks[t][ai][bi]=avoiding(R,C,iA,B,A,t);
                    int ibi=invidx[t][bi];
                    avoidPreprocess[t][ai][ibi]=
                            (avoidmasks[t][ai][bi]&movemask[t][ibi])==0;
                }
            }
        }

        System.out.println("pre-DP time="+(System.currentTimeMillis()-timest));

        timest=System.currentTimeMillis();
        class SparseMat {
            Map<Integer,BigInteger> vals;
            int R, C;
            SparseMat(int R, int C) {
                this.R=R; this.C=C;
                vals=new HashMap<>();
            }
            private RuntimeException idxerr(int r, int c) {
                return new RuntimeException(String.format("Sparse matrix out of bounds: (r,c)=(%d,%d), (R,C)=(%d,%d)",r,c,R,C));
            }
            public void set(int r, int c, BigInteger v) {
                if (0<=r&&r<R&&0<=c&&c<C) {
                    int i=r*C+c;
                    if (v.equals(BigInteger.ZERO)) vals.remove(i);
                    else vals.put(i,v);
                }
                else throw idxerr(r,c);
            }
            public BigInteger get(int r, int c) {
                if (0<=r&&r<R&&0<=c&&c<C) return vals.getOrDefault(r*C+c,BigInteger.ZERO);
                else throw idxerr(r,c);
            }
        }
        List<SparseMat[][]> dpa=new ArrayList<>(),
                dpb=new ArrayList<>();
        dpa.add(null);
        dpb.add(null);
        BigInteger target=BigInteger.ONE;
        for (int n=2; n<=R*C; n++) target=target.multiply(new BigInteger(""+n));
        target=target.divide(new BigInteger("2"));
        System.out.println("target="+target);
        BigInteger tot=BigInteger.ONE;
        System.out.println("0:"+tot);
        class DPValHelp {
            public BigInteger dpaval(int k, int t, int d, int ai, int bi) {
                if (k<2) throw new RuntimeException("k="+k+"<2");
                if (k==2) return d==sylcost[t][bi]+sylcost[1-t][ai]?BigInteger.ONE:BigInteger.ZERO;
                if (k==3) {
                    int tcost=d-(sylcost[t][bi]+sylcost[1-t][ai]);
                    return 0<=tcost&&tcost<sylcnt[t].length?
                            new BigInteger(""+(sylcnt[t][tcost]-(sylcost[t][invidx[t][bi]]==tcost?1:0))):
                            BigInteger.ZERO;
                }
                return dpa.get(k)[t][d].get(ai,bi);
            }
            public BigInteger dpbval(int k, int t, int d, int ai, int bi) {
                if (k<2) throw new RuntimeException("k="+k+"<2");
                if (k==2) return BigInteger.ZERO;
                if (k==3) {
                    int tcost=d-(sylcost[t][bi]+sylcost[1-t][ai]);
                    return sylcost[t][invidx[t][bi]]==tcost?BigInteger.ONE:BigInteger.ZERO;
                }
                return dpb.get(k)[t][d].get(ai,bi);
            }
        }
        DPValHelp $=new DPValHelp();
        int DMAX=10;
        List<BigInteger[][]> tots=new ArrayList<>();
        //tots(k,t,d)=total # good syllable sequences of k syllables, total move count d, last syllable of type t
        tots.add(null);
        int K=1;
        while (K<=DMAX) {
            tots.add(new BigInteger[2][DMAX+1]);
            dpa.add(new SparseMat[2][DMAX+1]);
            dpb.add(new SparseMat[2][DMAX+1]);
            /*
            dpa(k,t,d,A,B)=# d-move k-syllable sequences ending in ....C,A,B for any C!=inv(B), where C,B are type t and A is type (1-t)
            dpb(k,t,d,A,B)=# d-move k-syllable sequences ending in ....inv(B),A,B where B is type t and A is type (1-t)
            both expressions require that for all sets of consecutive syllables of the form inv(A) B A C, S(inv(A),B,A)&N(C)=empty

            Then:
            dpa(k,t,d,A,B)=(SUM_{C!=inv(B)} dpa(k-1,1-t,d-|B|,C,A)) + (SUM_{C!=inv(B) and S(inv(A),C,A)&M(B)==empty} dpb(k-1,1-t,d-|B|,C,A))
            dpb(k,t,d,A,B)=dpa(k-1,1-t,d-|B|,inv(B),A) + (dpb(k-1,1-t,d-|B|,inv(B),A) if S(inv(A),inv(B),A)&M(B)==empty else 0)

            k=3 is a base case. k=0,1,2 are dealt with separately

            To reduce running time, for each fixed (k,t), we define some helper variables:

            ha(d,A)=SUM_{C type t} dpa(k-1,1-t,d,C,A)
            hb(d,A,M)=SUM_{C type t and S(inv(A),C,A)&M==empty} dpb(k-1,1-t,d,C,A)

            Then dpa(k,t,d,A,B) simplifies to:
                ha(d-|B|,A)-dpa(k-1,1-t,d-|B|,inv(B),A) + hb(d-|B|,A,M(B))-(dpb(k-1,1-t,d-|B|,inv(B),A) if S(inv(A),inv(B),A)&M(B)==empty else 0)
             */
            for (int t=0; t<2; t++) {
                BigInteger[][] ha=new BigInteger[DMAX+1][nSyls[1-t]];
                BigInteger[][][] hb=new BigInteger[DMAX+1][nSyls[1-t]][1<<(t==0?R:C)];
                if (K>=4)
                for (int d=K-1; d<=DMAX; d++) for (int ai=0; ai<nSyls[1-t]; ai++) {
                    BigInteger va=BigInteger.ZERO;
                    for (int ci=0; ci<nSyls[t]; ci++)
                        va=va.add($.dpaval(K-1,1-t,d,ci,ai));
                    ha[d][ai]=va;
                    for (int mask=0; mask<(1<<(t==0?R:C)); mask++) {
                        BigInteger vb=BigInteger.ZERO;
                        for (int ci=0; ci<nSyls[t]; ci++)
                            if ((avoidmasks[t][ai][ci]&mask)==0)
                                vb=vb.add($.dpbval(K-1,1-t,d,ci,ai));
                        hb[d][ai][mask]=vb;
                    }
                }
                for (int d=K; d<=DMAX; d++) {
                    if (K==1)
                        tots.get(K)[t][d]=d<sylcnt[t].length?new BigInteger(""+sylcnt[t][d]):BigInteger.ZERO;
                    else if (K==2) {
                        long ret=0;
                        for (int d0=1; d0<d&&d0<sylcnt[t].length&&d-d0<sylcnt[1-t].length; d0++)
                            ret+=sylcnt[t][d0]*sylcnt[1-t][d-d0];
                        tots.get(K)[t][d]=new BigInteger(""+ret);
                    }
                    else if (K==3) {
                        BigInteger ret=BigInteger.ZERO;
                        for (int bi=0; bi<nSyls[t]; bi++) for (int ai=0; ai<nSyls[1-t]; ai++)
                            ret=ret.add($.dpaval(3,t,d,ai,bi)).add($.dpbval(3,t,d,ai,bi));
                        tots.get(K)[t][d]=ret;
                    }
                    else {
                        dpa.get(K)[t][d]=new SparseMat(nSyls[1-t],nSyls[t]);
                        dpb.get(K)[t][d]=new SparseMat(nSyls[1-t],nSyls[t]);
                        BigInteger ret=BigInteger.ZERO;
                        for (int ai=0; ai<nSyls[1-t]; ai++)
                        for (int bi=0; bi<nSyls[t]; bi++) {
                            int d1=d-sylcost[t][bi], ibi=invidx[t][bi];
                            if (d1>=K-1) {
                                BigInteger va=ha[d1][ai].subtract($.dpaval(K-1,1-t,d1,ibi,ai))
                                        .add(hb[d1][ai][movemask[t][bi]]);
                                if (avoidPreprocess[t][ai][bi]) va=va.subtract($.dpbval(K-1,1-t,d1,ibi,ai));
                                dpa.get(K)[t][d].set(ai,bi,va);
                                BigInteger vb=$.dpaval(K-1,1-t,d1,ibi,ai);
                                if (avoidPreprocess[t][ai][bi]) vb=vb.add($.dpbval(K-1,1-t,d1,ibi,ai));
                                dpb.get(K)[t][d].set(ai,bi,vb);
                                ret=ret.add(va).add(vb);
                            }
                        }
                        tots.get(K)[t][d]=ret;
                        System.out.println("# nonzero elems in dp("+K+","+t+","+d+"): "+dpa.get(K)[t][d].vals.size()+" "+dpb.get(K)[t][d].vals.size());
                    }
                }
                for (int k=1; k<=K; k++)
                    tot=tot.add(tots.get(k)[t][K]);
            }
            System.out.println(K+":"+tot+"\t (time (ms)="+(System.currentTimeMillis()-timest)+")");
            if (tot.compareTo(target)>=0) break;
            //delete unused dp arrays
            dpa.set(K-1,null);
            dpb.set(K-1,null);
            K++;
        }
        System.out.println("DP time="+(System.currentTimeMillis()-timest));
    }
}
