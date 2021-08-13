import java.math.BigInteger;
import java.util.*;
/**
 * given a start state S and end state E:
 *      ex. 5x5 Loopover states 11111x11111 and 00011x00011
 * along with a list of middle states M[]:
 *      ex. 00111x00111, 00111x01011, 10011x01011, etc.
 * use these midstates to find an upper bound on the God's number of transforming the starting state to the end state
 *
 * more formally, choose a threshold D
 * choose a midstate M[a] to be the "default"
 * then go through all scrambles such that naively using the two trees S-->M[a] and M[a]-->E yields a solution of >D moves
 * for each scramble:
 *      for each i!=a, try solving it with the trees S-->M[i] and M[i]-->E until a solution of <=D moves is found
 *      if a solution is not found, try applying an arbitrary sequence of prefix moves to the scramble,
 *          and then try solving it with the trees S-->M[i] and M[i]-->E (this time including i==a)
 *          repeat for all possible prefix sequences of length 1, 2, ... until a short enough solution is found
 */
public class LoopoverBFSImprove {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static int[] inv(int[] P) {
        int[] Q=new int[P.length];
        for (int i=0; i<P.length; i++) Q[P[i]]=i;
        return Q;
    }
    private static int[] prod(int[] A, int[] B) {
        //A is a permutation array
        //return [ A[B[i]] for all i]
        int[] out=new int[B.length];
        for (int i=0; i<B.length; i++)
            out[i]=A[B[i]];
        return out;
    }
    private static BigInteger perm2code(int[] A) {
        BigInteger n=BigInteger.ZERO;
        for (int i=0; i<A.length; i++)
            n=n.add(new BigInteger(""+A[i]).multiply(new BigInteger(""+A.length).pow(i)));
        return n;
    }
    private static int[] code2perm(BigInteger code, int N) {
        int[] P=new int[N];
        BigInteger h=code, nN=new BigInteger(""+N);
        for (int i=0; i<N; i++) {
            P[i]=h.mod(nN).intValue();
            h=h.divide(nN);
        }
        return P;
    }
    private static int[] restoringPerm(int[] P, int[] T) {
        //returns Q s.t. prod(P,Q)==T, null if no such Q exists
        Map<Integer,Integer> locs=new HashMap<>();
        for (int i=0; i<P.length; i++)
            locs.put(P[i],i);
        if (locs.size()!=P.length) throw new RuntimeException();
        //System.out.println(locs);
        int[] Q=new int[T.length];
        for (int i=0; i<T.length; i++)
            if (!locs.containsKey(T[i])) return null;
            else Q[i]=locs.get(T[i]);
        return Q;
    }
    private static String boardStr(int[] solvedscrm, int[] scrm, int R, int C) {
        int[] display=new int[R*C]; Arrays.fill(display,-1);
        for (int i=0; i<scrm.length; i++)
            display[scrm[i]]=solvedscrm[i];
        StringBuilder out=new StringBuilder();
        String form="%"+(R*C<=26?1:3)+"s";
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                out.append(String.format(form,display[r*C+c]==-1?".":(R*C<=26?""+(char)('A'+display[r*C+c]):(display[r*C+c]+1))));
            out.append('\n');
        }
        return out.toString();
    }
    private static int[] distinctScrambles(int R, int C, LoopoverBFS bfs0, int d0, LoopoverBFS bfs1) {
        List<int[]> transformations=new ArrayList<>();
        for (int di=0; di<R*C; di++) for (int r0=0; r0<2; r0++) for (int r1=0; r1<2; r1++) for (int r2=0; r2<2; r2++) {
            int[] S=new int[R*C];
            for (int r=0; r<R; r++) for (int c=0; c<C; c++) {
                int nr=(r+di/C)%R, nc=(c+di%C)%C;
                if (r0==1) nr=R-1-nr;
                if (r1==1) nc=C-1-nc;
                if (r2==1) {
                    int t=nr; nr=nc; nc=t;
                }
                S[r*C+c]=nr*C+nc;
            }
            if (restoringPerm(prod(S,bfs0.pcstosolve),bfs0.pcstosolve)!=null
                    &&restoringPerm(prod(S,bfs1.pcstosolve),bfs1.pcstosolve)!=null)
                transformations.add(S);
        }
        /*for (int[] S:transformations) {
            int[][] board=new int[R][C];
            for (int i=0; i<R*C; i++)
                board[S[i]/C][S[i]%C]=i;
            for (int r=0; r<R; r++) {
                for (int c=0; c<C; c++)
                    System.out.print((char)('A'+board[r][c]));
                System.out.println();
            }
            System.out.println("---");
        }*/
        List<Integer> codes=new ArrayList<>();
        boolean[] seen=new boolean[bfs0.ncombos];
        for (int c0:bfs0.codesAtDepth(d0)) if (!seen[c0]) {
            codes.add(c0);
            seen[c0]=true;
            int[] Pf=bfs0.codeCombo(c0), P=prod(bfs0.freeto(),Pf);
            for (int[] S:transformations) {
                int[] tP=prod(inv(S),prod(P,restoringPerm(prod(inv(S),bfs0.pcstosolve),bfs0.pcstosolve)));
                int[] tPf=prod(bfs0.tofree(),tP);
                for (int i:tPf) if (i<0) throw new RuntimeException();
                int nc0=bfs0.comboCode(tPf);
                if (bfs0.depth(nc0)!=d0) throw new RuntimeException();
                seen[nc0]=true;
            }
        }
        int[] out=new int[codes.size()];
        for (int i=0; i<out.length; i++) out[i]=codes.get(i);
        return out;
    }
    private static boolean improve(int R, int C, String ststate, String enstate, int threshold, String[] midstates, boolean computeAllscrms) {
        System.out.println(R+"x"+C+": "+ststate+" --> ... --> "+enstate+
                "\nthreshold="+threshold+", midstates="+Arrays.toString(midstates));
        //prefix move sequences
        int M=0;
        for (int c=0; c<ststate.length(); c++)
            if (ststate.charAt(c)=='1') M+=2;
        BigInteger nM=new BigInteger(""+M);
        int[][] mvs, mvactions, mvreduc;
        boolean[][] rcfree0=LoopoverBFS.parseState(ststate);
        mvs=new int[M][]; mvactions=new int[M][]; {
            int idx=0;
            for (int mr=0; mr<R; mr++)
                if (rcfree0[0][mr])
                    for (int s=-1; s<=1; s+=2) {
                        mvs[idx]=new int[] {0,mr,s};
                        mvactions[idx]=new int[R*C];
                        for (int r=0; r<R; r++)
                            for (int c=0; c<C; c++)
                                mvactions[idx][r*C+c]=r*C+(r==mr?mod(c+s,C):c);
                        idx++;
                    }
            for (int mc=0; mc<C; mc++)
                if (rcfree0[1][mc])
                    for (int s=-1; s<=1; s+=2) {
                        mvs[idx]=new int[] {1,mc,s};
                        mvactions[idx]=new int[R*C];
                        for (int r=0; r<R; r++)
                            for (int c=0; c<C; c++)
                                mvactions[idx][r*C+c]=(c==mc?mod(r+s,R):r)*C+c;
                        idx++;
                    }
        }
        mvreduc=LoopoverBFS.mvreduc(mvs);
        List<List<BigInteger>> fronts=new ArrayList<>();
        {
            int[] id=new int[R*C]; for (int i=0; i<R*C; i++) id[i]=i;
            fronts.add(new ArrayList<>(Arrays.asList(perm2code(id))));
        }
        Map<BigInteger,BigInteger> data=new HashMap<>();
        //data.get(code)=(code of parent scramble)*M+(id of previous move)
        data.put(fronts.get(0).get(0),new BigInteger("-2"));

        int A=midstates.length;
        long timest=System.currentTimeMillis();
        LoopoverBFS[][] trees=new LoopoverBFS[A][2];
        for (int a=0; a<A; a++) {
            trees[a][0]=new LoopoverBFS(R,C,ststate,midstates[a]);
            trees[a][1]=new LoopoverBFS(R,C,midstates[a],enstate);
            if (computeAllscrms)
                trees[a][0].computeAllActions();
        }
        System.out.println("total tree preprocessing time="+(System.currentTimeMillis()-timest));
        int bestidx=0; //decide which midstate minimizes the total # of scrambles we must process
        long bscr=Long.MAX_VALUE;
        for (int a=0; a<A; a++) {
            LoopoverBFS bfs0=trees[a][0], bfs1=trees[a][1];
            long scr=0;
            for (int d0=0; d0<trees[a][0].D; d0++) {
                int[] codes0=distinctScrambles(R,C,bfs0,d0,bfs1);
                for (int d1=0; d1<trees[a][1].D; d1++)
                    if (d0+d1>threshold)
                        scr+=codes0.length*(long)bfs1.codesAtDepth(d1).length;
            }
            System.out.println(midstates[a]+":"+scr);
            if (scr<bscr) {
                bscr=scr;
                bestidx=a;
            }
        }
        for (int a=0; a<A; a++) if (a!=bestidx) {
            trees[a][0].clearFronts();
            trees[a][1].clearFronts();
        }
        System.out.println("main midstate="+midstates[bestidx]);
        LoopoverBFS tree0=trees[bestidx][0], tree1=trees[bestidx][1];
        System.out.printf("total combos to improve=%,d%n",bscr);
        timest=System.currentTimeMillis();
        long ntrials=0, ntries=0, nskips=0, maxtries=0;
        for (int d0=0; d0<tree0.D; d0++) {
            int[] bin0=distinctScrambles(R,C,tree0,d0,tree1);
            for (int d1=0; d1<tree1.D; d1++) if (d0+d1>threshold) {
                int[] bin1=tree1.codesAtDepth(d1);
                long st=System.currentTimeMillis();
                int[][] scrms0=new int[bin0.length][], scrms1=new int[bin1.length][];
                for (int idx0=0; idx0<bin0.length; idx0++)
                    scrms0[idx0]=tree0.scrambleaction(bin0[idx0]);
                for (int idx1=0; idx1<bin1.length; idx1++)
                    scrms1[idx1]=tree1.scrambleaction(bin1[idx1]);
                System.out.println("memoizing scramble actions: "+(System.currentTimeMillis()-st)+" ms");
                System.out.println(d0+","+d1+": ncombos="+String.format("%,d",bin0.length*(long)bin1.length));
                long stage=1, mark0=10_000, mark=mark0;
                String form="%12s%20s%n";
                System.out.printf(form,"elapsed ms","#combos");
                long reps=0;
                st=System.currentTimeMillis();
                for (int idx0=0; idx0<bin0.length; idx0++)
                    for (int idx1=0; idx1<bin1.length; idx1++) {
                        int[] scrm1=scrms1[idx1], scrm0=scrms0[idx0];
                        //a piece in location i is moved to location scrm0[scrm1[i]]
                        boolean reduced=false;
                        //List<List<int[]>> seqs=new ArrayList<>();
                        ntrials++;
                        long ntries0=ntries;
                        for (int a=0; a<A; a++) if (a!=bestidx) {
                            ntries++;
                            //seqs.clear();
                            int code0=trees[a][0].codeAfterScramble(scrm0,scrm1);
                            //seqs.add(trees[a][0].solvemvs(code0));
                            int[] action0=trees[a][0].solveaction(code0);
                            int code1=trees[a][1].codeAfterScramble(action0,scrm0,scrm1);
                            //^^^ for some reason, using the above line (if a 3-parameter version of LoopoverBFS.codeAfterScramble() existed) is slower than creating the array group1[]
                            //seqs.add(trees[a][1].solvemvs(code1));
                            if (trees[a][0].depth(code0)+trees[a][1].depth(code1)<=threshold) {
                                reduced=true;
                                break;
                            }
                        }
                        if (!reduced)
                            PREFIXANDALTBLOCK:
                                    for (int depth=1;; depth++) {
                                        if (fronts.size()<=depth) {
                                            fronts.add(new ArrayList<>());
                                            for (BigInteger f:fronts.get(depth-1)) {
                                                int[] action=code2perm(f,R*C);
                                                int[] mvlist=mvreduc[data.get(f).compareTo(BigInteger.ZERO)<0?M:
                                                        data.get(f).mod(nM).intValue()];
                                                for (int mi:mvlist) {
                                                    BigInteger nf=perm2code(prod(mvactions[mi],action));
                                                    if (!data.containsKey(nf)) {
                                                        data.put(nf,f.multiply(nM).add(BigInteger.valueOf(mi)));
                                                        fronts.get(depth).add(nf);
                                                    }
                                                }
                                            }
                                            System.out.println("max depth-->"+depth+" (#scrambles="+fronts.get(depth).size()+")");
                                        }
                                        for (BigInteger f:fronts.get(depth)) {
                                            int[] prefixaction=code2perm(f,R*C);
                                            for (int a=0; a<A; a++) {
                                                ntries++;
                                    /*seqs.clear();
                                    seqs.add(new ArrayList<>());
                                    for (BigInteger code=f; code.compareTo(BigInteger.ZERO)>=0; code=data.get(code).divide(nM))
                                        seqs.get(0).add(mvs[code.mod(nM).intValue()]);*/
                                                int code0=trees[a][0].codeAfterScramble(prefixaction,scrm0,scrm1);
                                                //seqs.add(trees[a][0].solvemvs(code0));
                                                int code1=trees[a][1].codeAfterScramble(trees[a][0].solveaction(code0),prefixaction,scrm0,scrm1);
                                                //seqs.add(trees[a][1].solvemvs(code1));
                                                if (depth+trees[a][0].depth(code0)+trees[a][1].depth(code1)<=threshold)
                                                    break PREFIXANDALTBLOCK;
                                            }
                                        }
                                    }

                        maxtries=Math.max(maxtries,ntries-ntries0);
                    /*if (Math.random()<1/1000_000.0) {
                        int[] solvedscrm=new int[tree0.K+tree1.K];
                        System.arraycopy(tree0.pcstosolve,0,solvedscrm,0,tree0.K);
                        System.arraycopy(tree1.pcstosolve,0,solvedscrm,tree0.K,tree1.K);
                        System.out.print(boardStr(solvedscrm,prodperm(prodperm(solvedscrm.clone(),scrm1),scrm0),R,C));
                        for (List<int[]> tmp:seqs)
                            System.out.println(LoopoverBFS.mvseqStr(tmp));
                    }*/
                        reps++;
                        long time=System.currentTimeMillis()-st;
                        if (time>=mark) {
                            System.out.printf(form,String.format("%,d",time),String.format("%,d",reps));
                            stage++;
                            mark=(long)(mark0*Math.pow(stage,2.5));
                        }
                    }
                System.out.printf(form,String.format("%,d",System.currentTimeMillis()-st),String.format("%,d",reps));
            }
        }
        System.out.println("improvement time="+(System.currentTimeMillis()-timest));
        System.out.println("mean # alternate attempted solutions per scramble="+ntries+"/"+ntrials+"="+(ntries/(double)ntrials));
        System.out.println("maximum # attempts on a scramble="+maxtries);
        System.out.println("mean # skips per scramble="+nskips+"/"+ntrials+"="+(nskips/(double)ntrials));
        return true;
    }
    public static void main(String[] args) {
        //TODO: 5x5:0x0->3x3, 6x6:0x0->3x3
        long st=System.currentTimeMillis();
        List<String> mids=new ArrayList<>();
        for (int r=0; r<3; r++)
            for (int c=0; c<3; c++) {
                StringBuilder s=new StringBuilder("00011x00011");
                s.setCharAt(r,'1');
                s.setCharAt(6+c,'1');
                mids.add(s.toString());
            }
        LoopoverBFSImprove.improve(5,5,"11111x11111","00011x00011",
                20,
                mids.toArray(new String[0]),
                true
        );
        System.out.println("total program time="+(System.currentTimeMillis()-st));
    }
}
