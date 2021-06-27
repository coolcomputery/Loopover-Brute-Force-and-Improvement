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
    private static int[] inv(int[] P) {
        //return inverse permutation of P
        int[] I=new int[P.length];
        for (int i=0; i<P.length; i++)
            I[P[i]]=i;
        return I;
    }
    private static int[] prodperm(int[] A, int[] B) {
        int[] out=new int[A.length];
        for (int i=0; i<A.length; i++)
            out[i]=B[A[i]];
        return out;
    }
    private static void improve(int R, int C, String[] Rfrees, String[] Cfrees, int threshold, int P, boolean[] allActions) {
        System.out.println(R+"x"+C+"\n"+Arrays.toString(Rfrees)+","+Arrays.toString(Cfrees)+"\nthreshold="+threshold+", P="+P);
        int M=0;
        for (int mr=0; mr<R; mr++) if (Rfrees[0].charAt(mr)=='1') M+=2;
        for (int mc=0; mc<C; mc++) if (Cfrees[0].charAt(mc)=='1') M+=2;
        int[][] mvs=new int[M][], mvactions=new int[M][]; {
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
        int[][] mvreduc=LoopoverBFS.mvreduc(mvs);
        boolean[][] mvreducmat=new boolean[M][M];
        for (int m=0; m<M; m++) for (int m2:mvreduc[m]) mvreducmat[m][m2]=true;
        List<int[]> mvseqs=new ArrayList<>();
        //generate all possible (non-redundant) sequences of moves of length <=P
        for (int len=1; len<=P; len++) {
            int[] seq=new int[P];
            while (seq[P-1]<M) {
                boolean good=true;
                for (int p=0; p<P-1&&good; p++)
                    if (!mvreducmat[seq[p]][seq[p+1]])
                        good=false;
                if (good)
                    mvseqs.add(seq.clone());
                seq[0]++;
                for (int p=0; p<P-1&&seq[p]==P; p++) {
                    seq[p]=0;
                    seq[p+1]++;
                }
            }
        }
        List<int[]> mvseqactions=new ArrayList<>();
        for (int[] seq:mvseqs) {
            int[] ret=new int[R*C];
            for (int i=0; i<R*C; i++) ret[i]=i;
            for (int p=0; p<P; p++)
                ret=prodperm(ret,mvactions[seq[p]]);
            mvseqactions.add(ret);
        }
        System.out.println("#mvseqs="+mvseqs.size());

        //create BFS trees
        int T=Rfrees.length-1;
        LoopoverBFS[] trees=new LoopoverBFS[T];
        for (int si=0; si<Rfrees.length-1; si++)
            trees[si]=new LoopoverBFS(R,C,Rfrees[si],Cfrees[si],Rfrees[si+1],Cfrees[si+1]);
        for (int t=0; t<T-1; t++)
            if (allActions[t])
                trees[t].computeAllActions();
        //binnedCodes[t][d] contains the codes of all scrambles for tree t at depth d
        int[][][] binnedCodes=new int[T][][];
        for (int t=0; t<T; t++) {
            int D=trees[t].D, ncombos=trees[t].ncombos;
            int[] freqs=new int[D];
            for (int c=0; c<ncombos; c++) {
                int d=trees[t].depth(c);
                if (d!=-1) freqs[d]++;
            }
            binnedCodes[t]=new int[D][];
            for (int d=0; d<D; d++)
                binnedCodes[t][d]=new int[freqs[d]];
            int[] idxs=new int[D];
            for (int c=0; c<ncombos; c++) {
                int d=trees[t].depth(c);
                if (d!=-1) binnedCodes[t][d][idxs[d]++]=c;
            }
        }
        //the collection of all trees creates a total list of pieces that the trees collectively solve
        int tK=0; for (LoopoverBFS t:trees) tK+=t.K;
        int[] solvedscrm=new int[tK];
        int[] subarrstart=new int[T+1];
        for (int t=0, idx=0; t<T; t++) {
            subarrstart[t]=idx;
            for (int v:trees[t].pcstosolve)
                solvedscrm[idx++]=v;
        }
        subarrstart[T]=tK;
        System.out.println("solvedscrm="+Arrays.toString(solvedscrm));
        System.out.println("subarrstart="+Arrays.toString(subarrstart));
        List<int[]> depthSets=new ArrayList<>(); {
            long totcombos=0;
            int[] depths=new int[T];
            while (depths[T-1]<trees[T-1].D) {
                int totdepth=0; for (int d:depths) totdepth+=d;
                if (totdepth>threshold) {
                    long ncombos=1;
                    for (int t=0; t<T; t++) ncombos*=binnedCodes[t][depths[t]].length;
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
                for (int t=0; t<T; t++) ncombos*=binnedCodes[t][depths[t]].length;
                System.out.println(Arrays.toString(depths)+": ncombos="+ncombos);
            }
            int[][] bins=new int[T][];
            for (int t=0; t<T; t++)
                bins[t]=binnedCodes[t][depths[t]];
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
                    scrm=prodperm(scrm,inv(trees[t].solveaction(codes[t])));
                //scrm[i]=the location where the piece solvedscrm[i] goes to
                //the locations that all the pieces of trees[t].pcstosolve go to
                //  are described by the subarray scrm[subarrstart[t]]...scrm[subarrstart[t+1]-1]
                boolean reduced=false;
                //List<List<int[]>> seqs=new ArrayList<>();
                for (int mvsi=0; mvsi<mvseqactions.size()&&!reduced; mvsi++) {
                    int[] nscrm=prodperm(scrm,mvseqactions.get(mvsi));
                    int ntotdepth=mvseqs.get(mvsi).length;
                    /*seqs.clear();
                    seqs.add(mvseqs.get(mvsi));*/
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
                    int[] display=new int[R*C]; Arrays.fill(display,-1);
                    for (int i=0; i<tK; i++)
                        display[scrm[i]]=solvedscrm[i];
                    for (int r=0; r<R; r++) {
                        for (int c=0; c<C; c++)
                            System.out.print(display[r*C+c]==-1?'.':(char)('A'+display[r*C+c]));
                        System.out.println();
                    }
                    for (int t=0; t<T; t++) {
                        System.out.println("t="+t);
                        List<int[]> tmp=trees[t].solvemvs(codes[t]);
                        for (int[] mv:tmp) System.out.print(" "+Arrays.toString(mv));
                        System.out.println();
                    }
                    return;
                }
                /*{
                    int[] display=new int[R*C]; Arrays.fill(display,-1);
                    for (int i=0; i<tK; i++)
                        display[scrm[i]]=solvedscrm[i];
                    for (int r=0; r<R; r++) {
                        for (int c=0; c<C; c++)
                            System.out.print(display[r*C+c]==-1?'.':(char)('A'+display[r*C+c]));
                        System.out.println();
                    }
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
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        improve(6,6,
                new String[] {"000011","000011","000001"},
                new String[] {"000011","000001","000001"},
                //28,>6
                28,7,
                new boolean[] {true,true}
        );
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
