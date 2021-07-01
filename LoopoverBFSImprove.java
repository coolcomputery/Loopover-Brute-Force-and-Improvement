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
    private int R, C, tK, M;
    private LoopoverBFS tree0, tree1;
    private boolean[] computeAll;
    private int[][] mvs, mvactions, mvreduc;
    public LoopoverBFSImprove(int R, int C, String[] Rfrees, String[] Cfrees, boolean[] computeAll) {
        String display=R+"x"+C+"\n"+Arrays.toString(Rfrees)+","+Arrays.toString(Cfrees);
        if (Rfrees.length!=3||Cfrees.length!=3)
            throw new RuntimeException("Not supported: "+display);
        System.out.println(display);
        this.R=R; this.C=C;
        tree0=new LoopoverBFS(R,C,Rfrees[0],Cfrees[0],Rfrees[1],Cfrees[1]);
        tree1=new LoopoverBFS(R,C,Rfrees[1],Cfrees[1],Rfrees[2],Cfrees[2]);
        this.computeAll=computeAll;
        if (computeAll[0]) for (int D=0; D<tree0.D; D++) tree0.computeActions(D);
        if (computeAll[1]) for (int D=0; D<tree1.D; D++) tree1.computeActions(D);
        //the collection of all trees creates a total list of pieces that the trees collectively solve
        tK=tree0.K+tree1.K;
        M=0;
        for (int mr=0; mr<R; mr++) if (Rfrees[0].charAt(mr)=='1') M+=2;
        for (int mc=0; mc<C; mc++) if (Cfrees[0].charAt(mc)=='1') M+=2;
        mvs=new int[M][]; mvactions=new int[M][]; {
            int idx=0;
            for (int mr=0; mr<R; mr++)
                if (Rfrees[0].charAt(mr)=='1')
                    for (int s=-1; s<=1; s+=2) {
                        mvs[idx]=new int[] {0,mr,s};
                        mvactions[idx]=new int[R*C];
                        for (int r=0; r<R; r++)
                            for (int c=0; c<C; c++)
                                mvactions[idx][r*C+c]=r*C+(r==mr?mod(c+s,C):c);
                        idx++;
                    }
            for (int mc=0; mc<C; mc++)
                if (Cfrees[0].charAt(mc)=='1')
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
    }
    private boolean improve(int threshold, int P) {
        System.out.println("threshold="+threshold+", P="+P);
        //BFS over all nonredundant move sequences of length <=P
        List<int[]> mvseqs=new ArrayList<>(); List<int[]> mvseqactions=new ArrayList<>(); {
            List<int[]> mvseqfront=new ArrayList<>();
            mvseqfront.add(new int[] {});
            Set<String> seen=new HashSet<>();
            seen.add(Arrays.toString(scrambleAction(R,C,mvseqfront.get(0),mvactions)));
            for (int D=0; D<P; D++) {
                List<int[]> nmvseqfront=new ArrayList<>();
                for (int[] mseq:mvseqfront)
                    for (int mi:mvreduc[mseq.length==0?M:mseq[D-1]]) {
                        int[] nmseq=new int[D+1];
                        System.arraycopy(mseq,0,nmseq,0,D);
                        nmseq[D]=mi;
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
            }
        }
        System.out.println("#mvseqs="+mvseqs.size());

        List<int[]> depthSets=new ArrayList<>(); {
            long totcombos=0;
            for (int d0=0; d0<tree0.D; d0++)
                for (int d1=0; d1<tree1.D; d1++)
                    if (d0+d1>threshold) {
                        depthSets.add(new int[] {d0,d1});
                        totcombos+=tree0.codesAtDepth(d0).length*(long)tree1.codesAtDepth(d1).length;
                    }
            System.out.println("total combos to reduce="+totcombos);
        }

        for (int[] depths:depthSets) {
            int d0=depths[0], d1=depths[1];
            int[] bin0=tree0.codesAtDepth(d0), bin1=tree1.codesAtDepth(d1);
            System.out.println(Arrays.toString(depths)+": ncombos="+bin0.length*(long)bin1.length);
            long st=System.currentTimeMillis();
            if (!computeAll[0]) tree0.computeActions(d0);
            if (!computeAll[1]) tree1.computeActions(d1);
            System.out.println("memoizing scramble actions: "+(System.currentTimeMillis()-st)+" ms");
            long stage=0, mark0=5000, mark=mark0;
            String form="%12s%12s%n";
            System.out.printf(form,"elapsed ms","#combos");
            long reps=0;
            st=System.currentTimeMillis();
            for (int idx0=0; idx0<bin0.length; idx0++)
                for (int idx1=0; idx1<bin1.length; idx1++) {
                    int[] scrm1=tree1.scrambleaction(bin1[idx1]), scrm0=tree0.scrambleaction(bin0[idx0]);
                    //scrm[i]=scrm0[scrm1[solvedscrm[i]]]
                    //scrm[i]=the location where the piece solvedscrm[i] goes to
                    //where solvedscrm:=[tree0.pcstosolve | tree1.pcstosolve]
                    boolean reduced=false;
                    //List<List<int[]>> seqs=new ArrayList<>();
                    for (int mvsi=0; mvsi<mvseqactions.size()&&!reduced; mvsi++) {
                        int[] prefixaction=mvseqactions.get(mvsi);
                    /*seqs.clear();
                    seqs.add(new ArrayList<>());
                    for (int mi:mvseqs.get(mvsi))
                        seqs.get(0).add(mvs[mi]);*/
                        int[] subarr=new int[tree0.K];
                        for (int i=0; i<tree0.K; i++)
                            subarr[i]=prefixaction[scrm0[scrm1[tree0.pcstosolve[i]]]];
                        //seqs.add(tree0.solvemvs(subarr));
                        int[] tree0action=tree0.solveaction(subarr);
                        int[] subarr2=new int[tree1.K];
                        for (int i=0; i<tree1.K; i++)
                            subarr2[i]=tree0action[prefixaction[scrm0[scrm1[tree1.pcstosolve[i]]]]];
                        //seqs.add(tree1.solvemvs(subarr2));
                        int ntotdepth=mvseqs.get(mvsi).length+tree0.depth(subarr)+tree1.depth(subarr2);
                        if (ntotdepth<=threshold) reduced=true;
                    }
                    if (!reduced) {
                        System.out.println("NOT REDUCED:");
                        int[] solvedscrm=new int[tK];
                        System.arraycopy(tree0.pcstosolve,0,solvedscrm,0,tree0.K);
                        System.arraycopy(tree1.pcstosolve,0,solvedscrm,tree0.K,tree1.K);
                        System.out.print(boardStr(solvedscrm,prodperm(prodperm(solvedscrm.clone(),scrm1),scrm0),R,C));
                        LoopoverBFS[] trees={tree0,tree1};
                        int[] codes={bin0[idx0],bin1[idx1]};
                        for (int t=0; t<2; t++) {
                            System.out.print("t="+t+";");
                            List<int[]> tmp=trees[t].solvemvs(codes[t]);
                            for (int[] mv:tmp) System.out.print(" "+Arrays.toString(mv));
                            System.out.println();
                        }
                        return false;
                    }
                /*if (Math.random()<0.001) {
                    int[] solvedscrm=new int[tK];
                    System.arraycopy(tree0.pcstosolve,0,solvedscrm,0,tree0.K);
                    System.arraycopy(tree1.pcstosolve,0,solvedscrm,tree0.K,tree1.K);
                    System.out.print(boardStr(solvedscrm,prodperm(prodperm(solvedscrm.clone(),scrm1),scrm0),R,C));
                    for (List<int[]> tmp:seqs) {
                        for (int[] mv:tmp) System.out.print(" "+Arrays.toString(mv));
                        System.out.println();
                    }
                }*/
                    reps++;
                    long time=System.currentTimeMillis()-st;
                    if (time>=mark) {
                        System.out.printf(form,time,reps);
                        stage++;
                        mark=(long)(mark0*Math.exp(Math.sqrt(stage)));
                    }
                }
            System.out.printf(form,System.currentTimeMillis()-st,reps);
            //free up memory
            if (!computeAll[0]) tree0.clearActions(d0);
            if (!computeAll[1]) tree1.clearActions(d1);
        }
        return true;
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        LoopoverBFSImprove improver=new LoopoverBFSImprove(5,5,
                new String[] {"11111","00111","00011"},new String[] {"11111","00111","00011"},
                //new String[] {"00011","00001","00000"},new String[] {"00011","00001","00000"},
                new boolean[] {true,true}
        );
        for (int P=1; P<=20; P++) {
            if (!improver.improve(20,P))
                System.out.println("--------------------------------\n");
            else break;
        }
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
