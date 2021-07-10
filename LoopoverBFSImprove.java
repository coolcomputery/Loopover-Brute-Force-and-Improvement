import java.util.*;
/**
 * improved version of LoopoverBruteForce.java
 * given a length-3 chain of Loopover states:
 *      ex. (5,5,{},{})-->(5,5,{0,1,2},{0,1})-->(5,5,{0,1,2,3},{0,1,2})
 * make the BFS trees of every adjacent pair of states;
 * then find the upper bound on the total state transformation
 *      ex. (5,5,{},{})-->(5,5,{0,1,2,3},{0,1,2})
 *
 */
public class LoopoverBFSImprove {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static int[] prodperm(int[] A, int[] B) {
        //B is a permutation array
        //return [ B[A[i]] for all i]
        int[] out=new int[A.length];
        for (int i=0; i<A.length; i++)
            out[i]=B[A[i]];
        return out;
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
    private static int[] scrambleAction(int R, int C, int[] mvseq, int[][] mvactions) {
        int[] out=new int[R*C]; for (int i=0; i<R*C; i++) out[i]=i;
        for (int mvi:mvseq) out=prodperm(out,mvactions[mvi]);
        return out;
    }

    private int R, C, tK;
    private String ststate, enstate;
    private LoopoverBFS tree0, tree1;
    public LoopoverBFSImprove(int R, int C, String st0, String st1, String st2) {
        System.out.println(R+"x"+C+": "+st0+" --> "+st1+" --> "+st2);
        this.R=R; this.C=C;
        tree0=new LoopoverBFS(R,C,st0,st1);
        tree1=new LoopoverBFS(R,C,st1,st2);
        //the collection of all trees creates a total list of pieces that the trees collectively solve
        tK=tree0.K+tree1.K;
        ststate=st0;
        enstate=st2;
    }
    private boolean improve(int threshold, String[] midstates, boolean[] computeAllscrms) {
        //prefix move sequences
        int M=0;
        for (int c=0; c<ststate.length(); c++)
            if (ststate.charAt(c)=='1') M+=2;
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
        List<int[]> mvseqs=new ArrayList<>(),
                mvseqactions=new ArrayList<>(),
                mvseqfront=new ArrayList<>();
        mvseqfront.add(new int[] {});
        Set<String> seen=new HashSet<>();
        seen.add(Arrays.toString(scrambleAction(R,C,mvseqfront.get(0),mvactions)));
        int prefixDepth=0;

        int A=midstates.length;
        System.out.println("threshold="+threshold+", midstates="+Arrays.toString(midstates));

        long timest=System.currentTimeMillis();
        LoopoverBFS[][] trees=new LoopoverBFS[A][2];
        for (int a=0; a<A; a++) {
            trees[a][0]=new LoopoverBFS(R,C,ststate,midstates[a]);
            trees[a][1]=new LoopoverBFS(R,C,midstates[a],enstate);
            if (computeAllscrms[a])
                trees[a][0].computeAllActions();
        }
        System.out.println("total tree preprocessing time="+(System.currentTimeMillis()-timest));

        List<int[]> depthSets=new ArrayList<>(); {
            long totcombos=0;
            for (int d0=0; d0<tree0.D; d0++)
                for (int d1=0; d1<tree1.D; d1++)
                    if (d0+d1>threshold) {
                        depthSets.add(new int[] {d0,d1});
                        totcombos+=tree0.codesAtDepth(d0).length*(long)tree1.codesAtDepth(d1).length;
                    }
            System.out.printf("total combos to improve=%,d%n",totcombos);
        }

        timest=System.currentTimeMillis();
        long ntrials=0, ntries=0, nskips=0, maxtries=0;
        for (int[] depths:depthSets) {
            int d0=depths[0], d1=depths[1];
            int[] bin0=tree0.codesAtDepth(d0), bin1=tree1.codesAtDepth(d1);
            int[][] scrms0=new int[bin0.length][], scrms1=new int[bin1.length][];
            for (int idx0=0; idx0<bin0.length; idx0++)
                scrms0[idx0]=tree0.scrambleaction(bin0[idx0]);
            for (int idx1=0; idx1<bin1.length; idx1++)
                scrms1[idx1]=tree1.scrambleaction(bin1[idx1]);
            System.out.println(Arrays.toString(depths)+": ncombos="+bin0.length*(long)bin1.length);
            long st=System.currentTimeMillis();
            System.out.println("memoizing scramble actions: "+(System.currentTimeMillis()-st)+" ms");
            long stage=0, mark0=10_000, mark=mark0;
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
                    for (int a=0; a<A; a++) {
                        ntries++;
                        maxtries=Math.max(maxtries,a+1);
                        //seqs.clear();
                        int code0=trees[a][0].codeAfterScramble(scrm0,scrm1);
                        //seqs.add(trees[a][0].solvemvs(code0));
                        if (trees[a][0].depth(code0)+(trees[a][1].D-1)<=threshold) {
                            nskips++;
                            reduced=true;
                            break;
                        }
                        int[] action0=trees[a][0].solveaction(code0);
                        int[] group1=new int[trees[a][1].K];
                        for (int i=0; i<group1.length; i++)
                            group1[i]=action0[scrm0[scrm1[trees[a][1].pcstosolve[i]]]];
                        //int code1=trees[a][1].codeAfterScramble(action0,scrm0,scrm1);
                        //^^^ for some reason, using the above line (if a 3-parameter version of LoopoverBFS.codeAfterScramble() existed) is slower than creating the array group1[]
                        //seqs.add(trees[a][1].solvemvs(code1));
                        if (trees[a][0].depth(code0)+trees[a][1].depth(group1)<=threshold) {
                            reduced=true;
                            break;
                        }
                    }
                    if (!reduced)
                    for (int mvsi=0;; mvsi++) {
                        if (mvsi==mvseqactions.size()) {
                            List<int[]> nmvseqfront=new ArrayList<>();
                            for (int[] mseq:mvseqfront)
                                for (int mi:mvreduc[mseq.length==0?M:mseq[prefixDepth-1]]) {
                                    int[] nmseq=new int[prefixDepth+1];
                                    System.arraycopy(mseq,0,nmseq,0,prefixDepth);
                                    nmseq[prefixDepth]=mi;
                                    int[] action=scrambleAction(R,C,nmseq,mvactions);
                                    String code=Arrays.toString(action);
                                    if (!seen.contains(code)) {
                                        seen.add(code);
                                        nmvseqfront.add(nmseq);
                                        mvseqs.add(nmseq);
                                        mvseqactions.add(action);
                                    }
                                }
                            mvseqfront=nmvseqfront;
                            prefixDepth++;
                            System.out.println("prefixDepth-->"+prefixDepth);
                        }
                        ntries++;
                        int[] prefixaction=mvseqactions.get(mvsi);
//                        seqs.clear();
//                        seqs.add(new ArrayList<>());
//                        for (int mi:mvseqs.get(mvsi))
//                            seqs.get(0).add(mvs[mi]);
                        int[] subarr=new int[tree0.K];
                        for (int i=0; i<tree0.K; i++)
                            subarr[i]=prefixaction[scrm0[scrm1[tree0.pcstosolve[i]]]];
                        //seqs.add(tree0.solvemvs(subarr));
                        int code0=tree0.abscomboCode(subarr);
                        int[] tree0action=tree0.solveaction(code0);
                        int[] subarr2=new int[tree1.K];
                        for (int i=0; i<tree1.K; i++)
                            subarr2[i]=tree0action[prefixaction[scrm0[scrm1[tree1.pcstosolve[i]]]]];
                        //seqs.add(tree1.solvemvs(subarr2));
                        if (mvseqs.get(mvsi).length+tree0.depth(code0)+tree1.depth(subarr2)<=threshold) {
                            reduced=true;
                            break;
                        }
                    }
                    if (!reduced) {
                        System.out.println("NOT REDUCED:");
                        int[] solvedscrm=new int[tK];
                        System.arraycopy(tree0.pcstosolve,0,solvedscrm,0,tree0.K);
                        System.arraycopy(tree1.pcstosolve,0,solvedscrm,tree0.K,tree1.K);
                        System.out.print(boardStr(solvedscrm,prodperm(prodperm(solvedscrm.clone(),scrm1),scrm0),R,C));
                        LoopoverBFS[] tmp={tree0,tree1};
                        int[] codes={bin0[idx0],bin1[idx1]};
                        for (int t=0; t<2; t++)
                            System.out.println("t="+t+";"+LoopoverBFS.mvseqStr(tmp[t].solvemvs(codes[t])));
                        return false;
                    }
                    /*if (Math.random()<1/1000_000.0) {
                        int[] solvedscrm=new int[tK];
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
                        mark=(long)(mark0*Math.exp(Math.sqrt(stage)));
                    }
                }
            System.out.printf(form,System.currentTimeMillis()-st,reps);
        }
        System.out.println("improvement time="+(System.currentTimeMillis()-timest));
        System.out.println("mean # alternate block-building sequences/prefix move sequences to try per scramble="+ntries+"/"+ntrials+"="+(ntries/(double)ntrials));
        System.out.println("maximum # tries on any one scramble="+maxtries);
        System.out.println("mean # skips per scramble="+nskips+"/"+ntrials+"="+(nskips/(double)ntrials));
        System.out.println("max prefix sequence length needed="+prefixDepth);
        return true;
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        String midstate="01011x01011";
        LoopoverBFSImprove improver=new LoopoverBFSImprove(5,5,
                "11111x11111",midstate,"00011x00011"
        );
        List<String> mids=new ArrayList<>();
        for (int r=0; r<3; r++)
            for (int c=0; c<3; c++) {
                StringBuilder s=new StringBuilder("00011x00011");
                s.setCharAt(r,'1');
                s.setCharAt(6+c,'1');
                if (!s.toString().equals(midstate))
                mids.add(s.toString());
            }
        boolean[] tmp=new boolean[mids.size()];
        Arrays.fill(tmp,true);
        improver.improve(21,
                mids.toArray(new String[0]),
                tmp
        );
        System.out.println("total program time="+(System.currentTimeMillis()-st));
    }
}
