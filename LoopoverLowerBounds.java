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
    private static List<List<int[]>> binnedSyllables(int R, int C) {
        //time complexity: O(R^C)
        List<List<int[]>> syllables=new ArrayList<>();
        for (int d=0; d<=R*(C/2); d++)
            syllables.add(new ArrayList<>());
        int[] S=new int[R]; S[0]=1;
        while (S[R-1]<C) {
            int d=0; for (int r=0; r<R; r++) d+=Math.min(S[r],C-S[r]);
            syllables.get(d).add(Arrays.copyOf(S,R));
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

    Let N(A)={x|A[x]!=0} (works with horizontal/vertical syllables)
    The above requirement can be written as: S(V0,H0,V1)&N(H1)==empty

    Because doing this for all possible syllable triplets V0 H1 V1 is impractical for 5x5 Loopover ((5^5)^3=~30 billion states),
        we only use this new reduction technique for syllable triplets V H inv(V)


    dpa(d,k,A,B)=# d-move k-syllable sequences ending in ....C,A,B for any C!=inv(B)
    dpb(d,k,A,B)=# d-move k-syllable sequences ending in ....inv(B),A,B
    both expressions require that for all sets of consecutive syllables of the form inv(A) B A C, S(inv(A),B,A)&N(C)=empty

    Then:
    dpa(d,k,A,B)=(SUM_{C!=inv(B)} dpa(d-|B|,k-1,C,A)) + (SUM_{C!=inv(B),S(inv(A),C,A)&N(B)==empty} dpb(d-|B|,k-1,C,A))
    dpb(d,k,A,B)=dpa(d-|B|,k-1,inv(B),A) + (dpb(d-|B|,k-1,inv(B),A) if S(inv(A),inv(B),A)&N(B)==empty else 0)

    To optimize on memory, it is best to further split dpa and dpb each into two functions, based on the type of the final syllable B

    the cases k=0,1 are dealt with separately

    everything written above also applies for V0 H0 V1 H1 V2 (i.e. if the types of all syllables are reversed)
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
        List<List<List<int[]>>> binnedSyls=new ArrayList<>(Arrays.asList(
                binnedSyllables(R,C),binnedSyllables(C,R)
        ));
        for (int t=0; t<2; t++) {
            for (int d=0; d<binnedSyls.get(t).size(); d++)
                System.out.print(" "+d+":"+binnedSyls.get(t).get(d).size());
            System.out.println();
        }
        List<List<int[]>> syls=new ArrayList<>();
        for (int t=0; t<2; t++) {
            syls.add(new ArrayList<>());
            for (int d=1; d<binnedSyls.get(t).size(); d++)
                //exclude the trivial syllable (which has cost 0)
                syls.get(t).addAll(binnedSyls.get(t).get(d));
            System.out.println("t="+t+": "+syls.get(t).size()+" nontrivial syllables");
        }
        int[] nSyls=new int[2];
        for (int t=0; t<2; t++) nSyls[t]=syls.get(t).size();
        System.out.println("nSyls="+Arrays.toString(nSyls));
        //System.out.println(Arrays.toString(avoiding(5,5,new int[] {1,0,0,0,0},new int[] {1,0,0,0,0},new int[] {-1,0,0,0,0},0)));
        boolean[][][] avoidPreprocess=new boolean[2][][];
        int[][][] avoidmasks=new int[2][][];
        int[][] invidxs=new int[2][], movemasks=new int[2][], sylcosts=new int[2][];
        for (int t=0; t<2; t++) {
            invidxs[t]=new int[nSyls[t]];
            movemasks[t]=new int[nSyls[t]];
            sylcosts[t]=new int[nSyls[t]];
            for (int[] B:syls.get(t)) {
                int bi=idx(R,C,B,t);
                invidxs[t][bi]=idx(R,C,inv(R,C,B,t),t);
                movemasks[t][bi]=moving(R,C,B,t);
                sylcosts[t][bi]=cost(R,C,B,t);
            }
            avoidPreprocess[t]=new boolean[nSyls[1-t]][nSyls[t]];
            avoidmasks[t]=new int[nSyls[1-t]][nSyls[t]];
            for (int[] A:syls.get(1-t)) {
                int ai=idx(R,C,A,1-t);
                int[] iA=inv(R,C,A,1-t);
                for (int[] B:syls.get(t)) {
                    int bi=idx(R,C,B,t);
                    avoidPreprocess[t][ai][bi]=
                            (avoiding(R,C,iA,inv(R,C,B,t),A,t)&moving(R,C,B,t))==0;
                    avoidmasks[t][ai][bi]=avoiding(R,C,iA,B,A,t);
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
        List<List<SparseMat[][]>> dps=new ArrayList<>(Arrays.asList(dpa,dpb));
        dpa.add(null);
        dpb.add(null);
        BigInteger target=BigInteger.ONE;
        for (int n=2; n<=R*C; n++) target=target.multiply(new BigInteger(""+n));
        target=target.divide(new BigInteger("2"));
        System.out.println("target="+target);
        BigInteger tot=BigInteger.ONE;
        System.out.println("0:"+tot);
        class DPValHelp {
            public BigInteger dpaval(int D, int k, int t, int ai, int bi) {
                if (k<2) throw new RuntimeException("k="+k+"<2");
                if (k==2) return D==sylcosts[t][bi]+sylcosts[1-t][ai]?BigInteger.ONE:BigInteger.ZERO;
                if (k==3) {
                    int tcost=D-(sylcosts[t][bi]+sylcosts[1-t][ai]);
                    return 0<=tcost&&tcost<binnedSyls.get(t).size()?
                            new BigInteger(""+(binnedSyls.get(t).get(tcost).size()-(sylcosts[t][invidxs[t][bi]]==tcost?1:0))):
                            BigInteger.ZERO;
                }
                return dpa.get(D)[k][t].get(ai,bi);
            }
            public BigInteger dpbval(int D, int k, int t, int ai, int bi) {
                if (k<2) throw new RuntimeException("k="+k+"<2");
                if (k==2) return BigInteger.ZERO;
                if (k==3) {
                    int tcost=D-(sylcosts[t][bi]+sylcosts[1-t][ai]);
                    return sylcosts[t][invidxs[t][bi]]==tcost?BigInteger.ONE:BigInteger.ZERO;
                }
                return dpb.get(D)[k][t].get(ai,bi);
            }
        }
        DPValHelp $=new DPValHelp();
        int D=1;
        while (true) {
            for (List<SparseMat[][]> dp:dps) dp.add(new SparseMat[D+1][2]);
            for (int k=1; k<=D; k++) for (int t=0; t<2; t++) {
                if (k==1)
                    tot=tot.add(new BigInteger(""+(D<binnedSyls.get(t).size()?binnedSyls.get(t).get(D).size():0)));
                else if (k<=3) {
                    for (int bi=0; bi<nSyls[t]; bi++)
                    for (int ai=0; ai<nSyls[1-t]; ai++)
                        tot=tot.add($.dpaval(D,k,t,ai,bi)).add($.dpbval(D,k,t,ai,bi));
                }
                else {
                    dpa.get(D)[k][t]=new SparseMat(nSyls[1-t],nSyls[t]);
                    dpb.get(D)[k][t]=new SparseMat(nSyls[1-t],nSyls[t]);
                    if (k>=4)
                        System.out.println("D,k,t="+D+","+k+","+t);
                    BigInteger[][] ha=new BigInteger[D][];
                    //ha(D,A):=SUM_B2 dpa(D,k-1,1-t,B2,A)
                    for (int d1=k-1; d1<D; d1++) {
                        ha[d1]=new BigInteger[nSyls[1-t]];
                        Arrays.fill(ha[d1],BigInteger.ZERO);
                        for (int ai=0; ai<nSyls[1-t]; ai++)
                            for (int bi=0; bi<nSyls[t]; bi++)
                                ha[d1][ai]=ha[d1][ai].add($.dpaval(d1,k-1,1-t,bi,ai));//dpa.get(d1)[k-1][1-t].get(bi,ai));
                    }
                    BigInteger[][][] hb=null;
                    //hb(D,A,M):=SUM_{B2 s.t. avoiding(inv(A),B2,A)&M==empty} dpb(D,k-1,1-t,B2,A)
                    if (k>=4) {
                        hb=new BigInteger[D][][];
                        long st=System.currentTimeMillis();
                        long reps=0, mark=60000;
                        for (int d1=k-1; d1<D; d1++) {
                            hb[d1]=new BigInteger[nSyls[1-t]][1<<(t==0?R:C)];
                            for (int ai=0; ai<nSyls[1-t]; ai++) {
                                Arrays.fill(hb[d1][ai],BigInteger.ZERO);
                                for (int bi=0; bi<nSyls[t]; bi++) {
                                    int si=avoidmasks[t][ai][bi];
                                    for (int mi=0; mi<(1<<(t==0?R:C)); mi++)
                                        if ((mi&si)==0)
                                            hb[d1][ai][mi]=hb[d1][ai][mi].add($.dpbval(d1,k-1,1-t,bi,ai));//dpb.get(d1)[k-1][1-t].get(bi,ai));
                                }
                                reps++;
                                long time=System.currentTimeMillis()-st;
                                if (time>=mark) {
                                    mark+=60000;
                                    System.out.printf("%12d%12d%n",reps,time);
                                }
                            }
                        }
                        System.out.printf("%12d%12d%n",reps,System.currentTimeMillis()-st);
                    }

                    for (int bi=0; bi<nSyls[t]; bi++) {
                        int Bc=sylcosts[t][bi];
                        int ibi=invidxs[t][bi];
                        int mi=movemasks[t][bi];
                        for (int ai=0; ai<nSyls[1-t]; ai++) {
                            BigInteger aval=BigInteger.ZERO;
                            if (D-Bc>=k-1) {
                                aval=ha[D-Bc][ai].subtract($.dpaval(D-Bc,k-1,1-t,ibi,ai));//dpa.get(D-Bc)[k-1][1-t].get(ibi,ai));
                                if (k>=4) {
                                    aval=aval.add(hb[D-Bc][ai][mi]);
                                    if (avoidPreprocess[t][ai][bi])
                                        aval=aval.subtract($.dpbval(D-Bc,k-1,1-t,ibi,ai));//dpb.get(D-Bc)[k-1][1-t].get(ibi,ai));
                                }
                            }
                            //...inv(B) A B
                            BigInteger bval=BigInteger.ZERO;
                            if (D-Bc>=k-1) {
                                bval=bval.add($.dpaval(D-Bc,k-1,1-t,ibi,ai));//dpa.get(D-Bc)[k-1][1-t].get(ibi,ai));
                                if (k>=4) {
                                    //...inv(A) inv(B) A B
                                    if (avoidPreprocess[t][ai][bi])
                                        bval=bval.add($.dpbval(D-Bc,k-1,1-t,ibi,ai));//dpb.get(D-Bc)[k-1][1-t].get(ibi,ai));
                                }
                            }
                            dpa.get(D)[k][t].set(ai,bi,aval);
                            dpb.get(D)[k][t].set(ai,bi,bval);
                        }
                    }
                    for (List<SparseMat[][]> dp:dps)
                        for (BigInteger v:dp.get(D)[k][t].vals.values())
                            tot=tot.add(v);
                    System.out.println("# nonzero elems in dp("+D+","+k+","+t+"): "+dpa.get(D)[k][t].vals.size()+" "+dpb.get(D)[k][t].vals.size());
                }
            }
            System.out.println(D+":"+tot);
            if (tot.compareTo(target)>=0) {
                System.out.println("God's number lower bound="+D);
                break;
            }
            D++;
        }
        System.out.println("DP time="+(System.currentTimeMillis()-timest));
    }
}
