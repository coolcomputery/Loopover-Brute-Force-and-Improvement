import java.util.*;
/**
 * given a chain of Loopover states:
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
    private int R, C, T, tK, M;
    private LoopoverBFS[] trees;
    private int[] solvedscrm, subarrstart;
    private int[][] mvs, mvactions, mvreduc;
    public LoopoverBFSImprove(int R, int C, String[] Rfrees, String[] Cfrees, boolean[] allActions) {
        System.out.println(R+"x"+C+"\n"+Arrays.toString(Rfrees)+","+Arrays.toString(Cfrees));
        this.R=R; this.C=C;
        T=Rfrees.length-1;
        trees=new LoopoverBFS[T];
        for (int si=0; si<Rfrees.length-1; si++)
            trees[si]=new LoopoverBFS(R,C,Rfrees[si],Cfrees[si],Rfrees[si+1],Cfrees[si+1]);
        for (int t=0; t<T-1; t++)
            if (allActions[t])
                trees[t].computeAllActions();
        //the collection of all trees creates a total list of pieces that the trees collectively solve
        tK=0; for (LoopoverBFS t:trees) tK+=t.K;
        solvedscrm=new int[tK];
        subarrstart=new int[T+1];
        for (int t=0, idx=0; t<T; t++) {
            subarrstart[t]=idx;
            for (int v:trees[t].pcstosolve)
                solvedscrm[idx++]=v;
        }
        subarrstart[T]=tK;
        System.out.println("solvedscrm="+Arrays.toString(solvedscrm)+
                "\nsubarrstart="+Arrays.toString(subarrstart));
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
            int[] depths=new int[T];
            while (depths[T-1]<trees[T-1].D) {
                int totdepth=0; for (int d:depths) totdepth+=d;
                if (totdepth>threshold) {
                    long ncombos=1;
                    for (int t=0; t<T; t++) ncombos*=trees[t].codesAtDepth(depths[t]).length;
                    totcombos+=ncombos;
                    depthSets.add(depths.clone());
                }
                depths[0]++;
                for (int t=0; t<T-1&&depths[t]==trees[t].D; t++) {
                    depths[t]=0;
                    depths[t+1]++;
                }
            }
            System.out.println("total combos to reduce="+totcombos);
        }
        for (int[] depths:depthSets) {
            {
                long ncombos=1;
                for (int t=0; t<T; t++) ncombos*=trees[t].codesAtDepth(depths[t]).length;
                System.out.println(Arrays.toString(depths)+": ncombos="+ncombos);
            }
            int[][] bins=new int[T][];
            for (int t=0; t<T; t++)
                bins[t]=trees[t].codesAtDepth(depths[t]);
            int[] idxs=new int[T];
            long st=System.currentTimeMillis();
            long stage=0, mark0=5000, mark=mark0;
            String form="%12s%12s%n";
            System.out.printf(form,"elapsed ms","#combos");
            long reps=0;
            for (; idxs[T-1]<bins[T-1].length;) {
                int[] codes=new int[T];
                for (int t=0; t<T; t++)
                    codes[t]=bins[t][idxs[t]];
                int[] scrm=solvedscrm.clone();
                //rescramble this solved state
                for (int t=T-1; t>-1; t--)
                    scrm=prodperm(scrm,trees[t].scrambleaction(codes[t]));
                //scrm[i]=the location where the piece solvedscrm[i] goes to
                //the locations that all the pieces of trees[t].pcstosolve go to
                //  are described by the subarray scrm[subarrstart[t]]...scrm[subarrstart[t+1]-1]
                boolean reduced=false;
                //List<List<int[]>> seqs=new ArrayList<>();
                for (int mvsi=0; mvsi<mvseqactions.size()&&!reduced; mvsi++) {
                    int[] nscrm=prodperm(scrm,mvseqactions.get(mvsi));
                    int ntotdepth=mvseqs.get(mvsi).length;
                    /*seqs.clear();
                    seqs.add(new ArrayList<>());
                    for (int mi:mvseqs.get(mvsi))
                        seqs.get(0).add(mvs[mi]);*/
                    for (int t=0; t<T; t++) {
                        //TODO: CUT OUT PREFIX OF nscrm AFTER EACH PHASE OF SOLVING
                        int i=subarrstart[t], j=subarrstart[t+1];
                        int[] subarr=new int[j-i];
                        System.arraycopy(nscrm,i,subarr,0,j-i);
                        //seqs.add(trees[t].solvemvs(subarr));
                        ntotdepth+=trees[t].depth(subarr);
                        if (t<T-1) //<-- big reduction in elapsed time
                            nscrm=prodperm(nscrm,trees[t].solveaction(subarr));
                    }
                    if (ntotdepth<=threshold) reduced=true;
                }
                if (!reduced) {
                    System.out.println("NOT REDUCED:");
                    System.out.print(boardStr(solvedscrm,scrm,R,C));
                    for (int t=0; t<T; t++) {
                        System.out.println("t="+t);
                        List<int[]> tmp=trees[t].solvemvs(codes[t]);
                        for (int[] mv:tmp) System.out.print(" "+Arrays.toString(mv));
                        System.out.println();
                    }
                    return false;
                }
                /*if (Math.random()<0.000001) {
                    System.out.print(boardStr(solvedscrm,scrm,R,C));
                    for (List<int[]> tmp:seqs) {
                        for (int[] mv:tmp) System.out.print(" "+Arrays.toString(mv));
                        System.out.println();
                    }
                }*/
                idxs[0]++;
                for (int t=0; t<T-1&&idxs[t]==bins[t].length; t++) {
                    idxs[t]=0;
                    idxs[t+1]++;
                }
                reps++;
                long time=System.currentTimeMillis()-st;
                if (time>=mark) {
                    System.out.printf(form,time,reps);
                    stage++;
                    mark=(long)(mark0*Math.exp(Math.sqrt(stage)));
                }
            }
            System.out.printf(form,System.currentTimeMillis()-st,reps);
        }
        return true;
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        LoopoverBFSImprove improver=new LoopoverBFSImprove(6,6,
                new String[] {"111111","001111","000111"},
                new String[] {"111111","001111","000111"},
                new boolean[] {true,true}
        );
        for (int P=1; P<=5; P++) {
            if (!improver.improve(26,P))
                System.out.print("\n\n\n\n\n\n");
            else break;
        }
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
