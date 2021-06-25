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
        //each perm is a list P[] where P[i]=where element i goes to
        //product permutation of applying perm A, then perm B
        int[] out=new int[A.length];
        for (int i=0; i<A.length; i++)
            out[i]=B[A[i]];
        return out;
    }
    private static void improve(int R, int C, String[] Rfrees, String[] Cfrees, int threshold, int P) {
        int M=2*R+2*C;
        int[][] mvs=new int[M][], mvactions=new int[M][]; {
            int idx=0;
            for (int mr=0; mr<R; mr++)
            for (int s=-1; s<=1; s+=2) {
                mvs[idx]=new int[] {0,mr,s};
                mvactions[idx]=new int[R*C];
                for (int r=0; r<R; r++)
                for (int c=0; c<C; c++)
                    mvactions[idx][r*C+c]=r*C+(r==mr?mod(c+s,C):c);
                idx++;
            }
            for (int mc=0; mc<C; mc++)
            for (int s=-1; s<=1; s+=2) {
                mvs[idx]=new int[] {1,mc,s};
                mvactions[idx]=new int[R*C];
                for (int r=0; r<R; r++)
                for (int c=0; c<C; c++)
                    mvactions[idx][r*C+c]=(c==mc?mod(r+s,R):r)*C+c;
                idx++;
            }
        }
        List<int[]> mvseqs=new ArrayList<>();
        //generate all possible (non-redundant) sequences of moves of length <=P
        for (int len=1; len<=P; len++) {
            int[] seq=new int[P];
            while (seq[P-1]<M) {
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

        int T=Rfrees.length-1;
        LoopoverBFS[] trees=new LoopoverBFS[T];
        for (int si=0; si<Rfrees.length-1; si++)
            trees[si]=new LoopoverBFS(R,C,Rfrees[si],Cfrees[si],Rfrees[si+1],Cfrees[si+1]);
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
        int tK=0; for (LoopoverBFS t:trees) tK+=t.K;
        //the collection of all trees creates a total list of pieces that the trees collectively solve
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
        int[] depths=new int[T];
        while (depths[T-1]<trees[T-1].D) {
            int totdepth=0; for (int d:depths) totdepth+=d;
            if (totdepth>=threshold) {
                System.out.println(Arrays.toString(depths));
                {
                    long ncombos=1;
                    for (int t=0; t<T; t++) ncombos*=binnedCodes[t][depths[t]].length;
                    System.out.println("ncombos="+ncombos);
                }
                int[][] bins=new int[T][];
                for (int t=0; t<T; t++)
                    bins[t]=binnedCodes[t][depths[t]];
                int[] idxs=new int[T];
                while (idxs[T-1]<bins[T-1].length) {
                    int[] codes=new int[T];
                    for (int t=0; t<T; t++)
                        codes[t]=bins[t][idxs[t]];
                    int[] scrm=solvedscrm.clone();
                    //rescramble this solved state
                    for (int t=T-1; t>-1; t--)
                        scrm=prodperm(scrm,inv(trees[t].solveaction(codes[t])));
                    //scrm[i]=the location where the piece solvedscrm[i] goes to
                    //the locations that all the pieces of trres[t].pcstosolve go to
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
                            int i=subarrstart[t], j=subarrstart[t+1];
                            int[] subarr=new int[j-i];
                            for (int k=i; k<j; k++)
                                subarr[k-i]=nscrm[k];
                            //seqs.add(trees[t].solvemvs(subarr));
                            ntotdepth+=trees[t].depth(subarr);
                            if (trees[t].solvemvs(subarr).size()!=trees[t].depth(subarr))
                                throw new RuntimeException();
                            nscrm=prodperm(nscrm,trees[t].solveaction(subarr));
                        }
                        if (ntotdepth<threshold) reduced=true;
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
                    /*else {
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
                }
            }
            depths[0]++;
            for (int t=0; t<T-1&&depths[t]==trees[t].D; t++) {
                depths[t]=0;
                depths[t+1]++;
            }
        }
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        /*improve(5,5,
                new String[] {"11111","00111","00011"},
                new String[] {"11111","00011","00001"},
                29
        );*/
        improve(4,4,
                new String[] {"1111","0011","0000"},
                new String[] {"1111","0001","0000"},
                28,2
        );
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
