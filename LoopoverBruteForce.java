/*
every scramble of a full board is represented by an int array, usually called locs[],
such that locs[i]=the location of tile i in the scrambled board
every location on a RxC board that is on row r and column c is represented with the integer r*C+c
*/
import java.util.*;
public class LoopoverBruteForce {
    private static int mod(int n, int k) {
        int out=n%k;
        if (out<0)
            out+=k;
        return out;
    }
    //keep scramble as mapping of number->location
    private static void move(int[] locs, int R, int C, Move mv) {
        if (mv.horz) {
            for (int i=0; i<locs.length; i++) {
                int r=locs[i]/C;
                if (r==mod(mv.coord,R))
                    locs[i]=r*C+mod(locs[i]%C+mv.shift,C);
            }
        }
        else {
            for (int i=0; i<locs.length; i++) {
                int c=locs[i]%C;
                if (c==mod(mv.coord,C))
                    locs[i]=mod(locs[i]/C+mv.shift,R)*C+c;
            }
        }
    }
    private static void move(int[] locs, int R, int C, ArrayList<Move> mvs) {
        for (Move mv:mvs)
            move(locs,R,C,mv);
    }
    private static void transform(int[] locs, int[] scrambleAction) {
        //locs is current scramble, scrambleAction is operation that will change locs (kind of like composing permutations but slightly different)
        for (int i=0; i<locs.length; i++)
            locs[i]=scrambleAction[locs[i]];
    }
    private static int transd(int loc, int R, int C, int tr, int tc) {
        return mod(loc/C+tr,R)*C+mod(loc%C+tc,C);
    }
    private static void print(int[] scramble, int C) {
        int[] perm=new int[scramble.length];
        for (int i=0; i<scramble.length; i++)
            perm[scramble[i]]=i;
        for (int i = 0; i < C; i++) {
            for (int j = 0; j < C; j++)
                System.out.printf("%4d", perm[i * C + j]);
            System.out.println();
        }
    }
    /*
    takes two trees, enumerates all scrambles that lead to a solution of length >=D,
    and tries solving each scramble by building the block starting from a different location
    */
    private static void improve(Tree[] trees, int D) {
        long st=System.currentTimeMillis();
        int N=trees[0].R;
        ArrayList<int[]> depthSets=new ArrayList<>();
        for (int d0 = trees[0].levelCnt-1; d0>-1; d0--)
            for (int d1 = trees[1].levelCnt-1; d1>-1 && d0+d1>=D; d1--) {
                depthSets.add(new int[]{d0, d1});
            }
        //express sequences of moves as permutation operators to speed up performing a predetermined sequence of moves on a scramble
        //save these operators in a table to avoid recomputing them
        int[][][] scrambleActions=new int[trees.length][][];
        int[][][] codesAtDepth=new int[trees.length][][];
        for (int stage=0; stage<trees.length; stage++) {
            ArrayList<ArrayList<Integer>> codeByDepth=new ArrayList<>();
            for (int i=0; i<trees[stage].levelCnt; i++)
                codeByDepth.add(new ArrayList<>());
            boolean[] usedDepth=new boolean[trees[stage].levelCnt];
            for (int[] set:depthSets)
                usedDepth[set[stage]]=true;
            for (int code=0; code<trees[stage].permsAmt; code++) {
                if (trees[stage].improved[code])
                    continue;
                int depth=trees[stage].depth(code);
                if (usedDepth[depth])
                    codeByDepth.get(depth).add(code);
            }
            codesAtDepth[stage]=new int[trees[stage].levelCnt][];
            for (int depth=0; depth<trees[stage].levelCnt; depth++) {
                codesAtDepth[stage][depth]=new int[codeByDepth.get(depth).size()];
                for (int i=0; i<codeByDepth.get(depth).size(); i++)
                    codesAtDepth[stage][depth][i]=codeByDepth.get(depth).get(i);
            }
        }
        long tot=0;
        for (int[] set:depthSets) {
            long prod=1;
            for (int stage=0; stage<set.length; stage++)
                prod*=codesAtDepth[stage][set[stage]].length;
            tot+=prod;
        }
        System.out.println("tot="+tot);
        for (int stage=0; stage<trees.length; stage++) {
            boolean[] triedDepth=new boolean[trees[stage].levelCnt+1];
            scrambleActions[stage]=new int[trees[stage].permsAmt][];
            for (int[] set:depthSets) {
                int depth=set[stage];
                if (triedDepth[depth])
                    continue;
                for (int code:codesAtDepth[stage][depth]) {
                    //System.out.println("scramble="+Arrays.toString(trees[stage].scramble(code)));
                    ArrayList<Move> mvs=trees[stage].solution(code);
                    int[] scramble = new int[N * N];
                    for (int i = 0; i < scramble.length; i++)
                        scramble[i] = i;
                    move(scramble, N, N, Move.inv(mvs));
                    //System.out.println("full scramble="+Arrays.toString(scramble));
                    scrambleActions[stage][code]=scramble;
                }
                triedDepth[depth]=true;
            }
        }
        int[][][] tree0_shiftedSolutions=new int[trees[0].permsAmt][N*N][];
        System.out.println(System.currentTimeMillis()-st+" ms (depthSets initialisation)");
        st=System.currentTimeMillis();
        int n_maxdepth=0;
        double depth_toprint=700_000;
        long scrambleCnt=0;
        int used=0;
        System.out.printf("%15s%25s%9s%n","scrambles done","shifted transforms used","ms");
        for (int[] set:depthSets) {
            int[] tree0_codes=codesAtDepth[0][set[0]], tree1_codes=codesAtDepth[1][set[1]];
            for (int code0:tree0_codes) {
                for (int code1:tree1_codes) {
                    int[] scramble=scrambleActions[1][code1];
                    transform(scramble,scrambleActions[0][code0]);
                    int bdepth=Integer.MAX_VALUE;
                    for (int ti=1; ti<N*N; ti++) {
                        int tr=ti/N, tc=ti%N;
                        int[] tscramble=scramble.clone();
                        int totdepth=0;
                        int[] wanted_locs=trees[0].wanted_locs;
                        int[] nsc=new int[wanted_locs.length];
                        for (int i=0; i<wanted_locs.length; i++)
                            nsc[i] = transd(tscramble[transd(wanted_locs[i],N,N,tr,tc)],N,N,-tr,-tc);
                        int nsc_code=trees[0].code(nsc);
                        totdepth+=trees[0].depth(nsc_code);
                        if (totdepth+trees[1].levelCnt-1<=D-1)
                            //skip early in this case
                            totdepth+=trees[1].levelCnt-1;
                        else {
                            if (tree0_shiftedSolutions[nsc_code][ti]==null) {
                                ArrayList<Move> mvs = trees[0].solution(nsc_code);
                                for (int i = 0; i < mvs.size(); i++)
                                    mvs.set(i, mvs.get(i).transd(tr, tc));
                                int[] tmp = new int[N * N];
                                for (int i = 0; i < tmp.length; i++)
                                    tmp[i] = i;
                                move(tmp, N, N, mvs);
                                //System.out.println("full scramble="+Arrays.toString(scramble));
                                tree0_shiftedSolutions[nsc_code][ti]=tmp;
                                used++;
                            }
                            //move(tscramble,N,N,mvs);
                            transform(tscramble,tree0_shiftedSolutions[nsc_code][ti]);
                            wanted_locs=trees[1].wanted_locs;
                            nsc=new int[wanted_locs.length];
                            for (int i=0; i<wanted_locs.length; i++)
                                nsc[i] = transd(tscramble[transd(wanted_locs[i],N,N,tr,tc)],N,N,-tr,-tc);
                            totdepth+=trees[1].depth(trees[1].code(nsc));
                        }
                        if (totdepth<bdepth) {
                            bdepth=totdepth;
                            if (bdepth<=D-1)
                                //only necessary to improve it down to D-1 moves since other scrambles of initial depth D-1 won't be improved anyway
                                break;
                        }
                    }
                    n_maxdepth=Math.max(n_maxdepth,bdepth);
                    if (bdepth==D) {
                        System.out.println("NOT IMPROVED:");
                        print(scramble,N);
                    }
                    scrambleCnt++;
                    if (scrambleCnt>=depth_toprint) {
                        System.out.printf("%15d%25d%9d%n",scrambleCnt,used,(System.currentTimeMillis()-st));
                        depth_toprint*=1.5;
                    }
                }
            }
        }
        System.out.println(System.currentTimeMillis()-st+" ms (improving 2 trees)");
        System.out.println(scrambleCnt+" scrambles of depth>="+D+" are now depth<="+n_maxdepth);
    }
    //eliminates all permutations that can be avoided by solving an offset set of tiles in fewer moves
    private static void improve(Tree tree, int D) {
        long st=System.currentTimeMillis();
        //ONLY WORKS IF TREE DESCRIBES BUILDING A SOLVED REGION FROM NO SOLVED REGION
        //take all perms with depth >=D and remove those that can be avoided by building translated of themselves that have smaller depth
        boolean[] code_improved=new boolean[tree.permsAmt];
        int R=tree.R, C=tree.C;
        if (tree.spaces!=R*C)
            throw new RuntimeException("Invalid tree.");
        System.out.println("improving "+tree.rowDo+";"+tree.colDo);
        boolean[] WANTED=new boolean[R*C];
        for (int loc:tree.wanted_locs)
            WANTED[loc]=true;
        int[] trans_uniques=new int[R*C];
        int[][] transd_wanted_locs_table=new int[R*C][];
        for (int i=0; i<R*C; i++) {
            int tr=i/C, tc=i%C;
            int unique=0;
            int[] transd=new int[tree.wcnt];
            for (int j=0; j<transd.length; j++)
                transd[j]=transd(tree.wanted_locs[j],R,C,tr,tc);
            transd_wanted_locs_table[i]=transd;
            for (int loc:tree.wanted_locs)
                if (!WANTED[transd(loc,R,C,tr,tc)])
                    unique++;
            trans_uniques[i]=unique;
        }
        Integer[] sorted_trans=new Integer[R*C-1];
        for (int i=1; i<R*C; i++)
            sorted_trans[i-1]=i;
        Arrays.sort(sorted_trans, new Comparator<Integer>() {
            @Override
            public int compare(Integer o1, Integer o2) {
                return trans_uniques[o1]-trans_uniques[o2];
            }
        });
        double reps_toprint=1000;
        for (int code=0, reps=0; code<tree.permsAmt; code++) {
            if (tree.depth(code)<D)
                continue;
            int[] oldScramble=tree.scramble(code);
            int[] pc_loc=new int[R*C];
            for (int i=0; i<R*C; i++)
                pc_loc[i]=-1;
            for (int i=0; i< oldScramble.length; i++)
                pc_loc[tree.wanted_locs[i]]=oldScramble[i];
            boolean[] occupied=new boolean[R*C];
            for (int loc:oldScramble)
                occupied[loc]=true;
            int spacesLeft=tree.spaces-tree.wcnt;
            int[] id_locLeft=new int[spacesLeft];
            //map id # to actual location that is not occupied by
            for (int i=0, id=0; i<R*C; i++) {
                if (!occupied[i]) {
                    id_locLeft[id]=i;
                    id++;
                }
            }
            int baseline=tree.depth(code);
            for (int trans:sorted_trans) {
                int tr=trans/C, tc=trans%C;
                int worstCaseDepth=0;
                int[] transd_wanted_locs=transd_wanted_locs_table[trans];
                int maxCode=1;
                for (int cnt=0; cnt<trans_uniques[trans]; cnt++)
                    maxCode*=spacesLeft-cnt;
                for (int ncode=0; ncode<maxCode; ncode++) {
                    int[] uniquePcs_locs=Tree.decoded(ncode,spacesLeft,trans_uniques[trans]);
                    for (int i=0; i<uniquePcs_locs.length; i++)
                        uniquePcs_locs[i]=id_locLeft[uniquePcs_locs[i]];
                    int[] n_pcLoc=pc_loc.clone();
                    int cntr=0;
                    for (int loc:transd_wanted_locs)
                        if (!WANTED[loc]) {
                            n_pcLoc[loc] = uniquePcs_locs[cntr];
                            cntr++;
                        }
                    int[] nscramble=new int[tree.wcnt];
                    for (int i=0; i<tree.wcnt; i++)
                        nscramble[i]=transd(n_pcLoc[transd_wanted_locs[i]],R,C,-tr,-tc);
                    int depth=tree.depth(tree.code(nscramble));
                    worstCaseDepth=Math.max(worstCaseDepth,depth);
                    if (worstCaseDepth>=tree.depth(code))
                        break;
                }
                if (worstCaseDepth<baseline) {
                    code_improved[code]=true;
                    break;
                }
                //System.out.println("worst case="+worstCaseDepth);
            }
            reps++;
            if (reps>=reps_toprint) {
                System.out.println(reps+" tried ("+(System.currentTimeMillis()-st)+")...");
                reps_toprint*=1.5;
            }
        }
        tree.improved=code_improved;
        int[] depth_distr=new int[tree.levelCnt];
        for (int i=0; i<tree.permsAmt; i++)
            if (!code_improved[i])
                depth_distr[tree.depth(i)]++;
        System.out.println(Arrays.toString(depth_distr));
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        //Tree[] trees={new Tree("11000","11100"), new Tree("xx100","xxx10")};
        Tree[] trees={new Tree("1100","1110"),new Tree("xx11","xxx1")};
        System.out.println(System.currentTimeMillis()-st+" ms (BFS)");
        st=System.currentTimeMillis();
        improve(trees[0],1);
        System.out.println(System.currentTimeMillis()-st+" ms (improving 1 tree)");
        improve(trees,24);
    }
    /*
    say you want to solve a subset of all the tiles
    ex. in 4x4 (where R=4, C=4) you want to solve the 2x3 block whose upper-left corner is (0,0)
    all the tiles in the 4x4 are like this:
    0  1  2  3
    4  5  6  7
    8  9  10 11
    12 13 14 15
    the 2x3 block thus consists of the pieces 0, 1, 2, 4, 5, and 6
    the 2x3 block is represented as rowDo=1100, colDo=1110 because it consists of all pieces that belong to the first two rows and the first three columns
    0  1  2  -
    4  5  6  -
    -  -  -  -
    -  -  -  -
    the respective Tree object with the value new Tree("1100","1110") contains every possible scramble of the pieces 0, 1, 2, 4, 5, and 6,
    the so-called "wanted pieces"
    these wanted pieces are kept in the array wanted_locs, which in this example equals [0, 1, 2, 4, 5, 6]
    every possible scramble containing only these wanted pieces is represented as an int array with the same length as wanted_locs
    such that element i of this scramble is the location of the tile wanted_locs[i]
    ex. the scramble [10, 14, 2, 8, 9, 13] translates to:
    -  -  2  -
    -  -  -  -
    4  5  0  -
    -  6  1  -
    every scramble is stored in the Tree by converting it into a 64-bit integer
    
    the Tree will start with the identity scramble, where all the wanted pieces are solved, and perform a breadth-first search (BFS) to all other permutations via Loopover single-turn moves
    each permutation must remember what permutation led to it in the BFS, what Loopover move led to it, and at what depth it was in the search tree
    this info is also compressed in a 64-bit integer
    */
    private static class Tree {
        //brute force all ways of expanding a partially solved board to one with more
        private static int encoded(int[] pperm, int n) {
            int[] help=new int[n];
            for (int i=0; i<n; i++)
                help[i]=i;
            int[] loc=help.clone();
            int out=0;
            for (int i=n-1; i>n-1-pperm.length; i--) {
                int id=pperm[i-(n-pperm.length)];
                int place=loc[id];
                out*=i+1;
                out+=place;
                //swap
                int tmp=help[place];
                int last=help[i];
                loc[last]=place;
                loc[tmp]=i;
                help[place]=last;
                help[i]=tmp;
            }
            return out;
        }
        private static int[] decoded(int code, int n, int k) {
            int[] swapidxs=new int[n];
            for (int help=code, id=n-k; id<n; id++) {
                swapidxs[id]=(help%(id+1));
                help/=id+1;
            }
            int[] perm=new int[n];
            for (int i=0; i<n; i++)
                perm[i]=i;
            for (int id=n-1; id>n-1-k; id--) {
                int tmp=perm[id];
                perm[id]=perm[swapidxs[id]];
                perm[swapidxs[id]]=tmp;
            }
            int[] out=new int[k];
            for (int i=0; i<k; i++)
                out[i]=perm[i+n-k];
            return out;
        }
        private static final char LOCKED='x', WANTED='1';
        String rowDo, colDo;
        int R, C, spaces, wcnt, permsAmt;
        int[] loc_id, //map an actual location in the RxC board to a number of a smaller range (index of a non-locked location)
                id_loc;
        int[] wanted_locs; //locations of the pieces that are going to be solved, in order
        long[] data;
        int levelCnt; //# of levels in BFS (includes solved permutation)
        //LOCKED = row/col already solved, do not touch
        //WANTED = row/col we want to solve
        //else= ignore
        boolean[] improved; //used in void improve(Tree tree, int D)
        private long compressed(Move mv, int depth, int par) {
            long out=depth;
            out*=2*R*C;
            out+=mv.horz?(mod(mv.coord,R)*C+mod(mv.shift,C)):(mod(mv.coord,C)*R+mod(mv.shift,R)+R*C);
            out*=2;
            out+=mv.horz?0:1;
            out*=permsAmt;
            out+=par;
            return out;
        }
        private Move get_move(int code) {
            long help=data[code]/permsAmt;
            boolean horz=help%2==0;
            help/=2;
            help%=2*R*C;
            if (!horz)
                help-=R*C;
            int len=horz?C:R;
            int coord=(int)help/len, shift=(int)help%len;
            return new Move(horz,coord,shift);
        }
        public int depth(int code) {
            return (int)(data[code]/permsAmt/2/(2*R*C));
        }
        public Tree(String rowDo, String colDo) {
            System.out.println(rowDo);
            System.out.println(colDo);
            this.rowDo =rowDo;
            this.colDo =colDo;
            R=rowDo.length();
            C=colDo.length();
            int l_rcnt=0, l_ccnt=0, w_rcnt=0, w_ccnt=0;
            for (int r=0; r<R; r++) {
                char st=rowDo.charAt(r);
                if (st==LOCKED)
                    l_rcnt++;
                else if (st==WANTED)
                    w_rcnt++;
            }
            for (int c=0; c<C; c++) {
                char st=colDo.charAt(c);
                if (st==LOCKED)
                    l_ccnt++;
                else if (st==WANTED)
                    w_ccnt++;
            }
            int lcnt=l_rcnt*l_ccnt;
            wcnt=w_rcnt*l_ccnt+w_ccnt*l_rcnt+w_rcnt*w_ccnt;
            spaces=R*C-lcnt;
            permsAmt =1;
            for (int cnt=0; cnt<wcnt; cnt++)
                permsAmt *=spaces-cnt;
            System.out.println(permsAmt);
            data=new long[permsAmt];
            improved=new boolean[permsAmt]; //DO NOT TOUCH THIS IN THIS CONSTRUCTOR
            for (int i=0; i<permsAmt; i++)
                data[i]=-1;
            //map each location to id [0,spaces)
            loc_id=new int[R*C];
            for (int i=0, id=0; i<R*C; i++)
                if (rowDo.charAt(i/C)==LOCKED && colDo.charAt(i%C)==LOCKED)
                    loc_id[i]=-1;
                else {
                    loc_id[i] = id;
                    id++;
                }
            id_loc=new int[spaces];
            for (int loc=0; loc<R*C; loc++)
                if (loc_id[loc]!=-1)
                    id_loc[loc_id[loc]]=loc;
            int[] solved=new int[wcnt];
            for (int i=0, id=0; i<R*C; i++) {
                int r=i/C, c=i%C;
                char rst=rowDo.charAt(r), cst=colDo.charAt(c);
                if ((rst==LOCKED || rst==WANTED) && (cst==LOCKED || cst==WANTED) && !(rst==LOCKED && cst==LOCKED)) {
                    solved[id]=i;
                    id++;
                }
            }
            wanted_locs=solved.clone();
            //System.out.println(Arrays.toString(wanted_locs));
            int solved_code=code(solved);
            data[solved_code]=compressed(new Move(true,0,0),0,0);
            int[] scrambleCodes=new int[] {solved_code};
            int reached=1;
            for (int depth=1; true; depth++) {
                int[] level=new int[permsAmt];
                int level_sz=0;
                double idx_toprint=3000_000;
                int idx=0;
                for (int parentCode:scrambleCodes) {
                    int[] sc=scramble(parentCode);
                    for (int r=0; r<R; r++)
                        if (rowDo.charAt(r)!=LOCKED)
                            for (int shift = -1; shift <= 1; shift += 2) {
                                int[] nsc = sc.clone();
                                Move mv = new Move(true, r, shift);
                                move(nsc, R, C, mv);
                                int code = code(nsc);
                                if (data[code]==-1) {
                                    data[code]=compressed(mv,depth,parentCode);
                                    level[level_sz]=code;
                                    level_sz++;
                                }
                            }
                    for (int c=0; c<C; c++)
                        if (colDo.charAt(c)!=LOCKED)
                            for (int shift = -1; shift <= 1; shift += 2) {
                                int[] nsc = sc.clone();
                                Move mv = new Move(false, c, shift);
                                move(nsc, R, C, mv);
                                int code = code(nsc);
                                if (data[code]==-1) {
                                    data[code]=compressed(mv,depth,parentCode);
                                    level[level_sz]=code;
                                    level_sz++;
                                }
                            }
                    idx++;
                    if (idx>=idx_toprint) {
                        System.out.println("i "+idx);
                        idx_toprint*=1.5;
                        //idx_toprint+=2_000_000;
                    }
                }
                reached+=level_sz;
                if (level_sz>0) {
                    int[] trimmed=new int[level_sz];
                    System.arraycopy(level,0,trimmed,0,level_sz);
                    scrambleCodes=trimmed;
                    System.out.println(depth + ": " + level_sz);
                }
                else {
                    levelCnt =depth;
                    break;
                }
            }
            System.out.println("reached="+reached);
            System.out.println("permsAmt="+ permsAmt);
        }
        private int code(int[] scramble) {
            int[] converted=new int[scramble.length];
            for (int i=0; i<scramble.length; i++)
                converted[i]=loc_id[scramble[i]];
            return encoded(converted,spaces);
        }
        private int[] scramble(int code) {
            int[] toconvert=decoded(code,spaces,wcnt);
            for (int i=0; i<toconvert.length; i++)
                toconvert[i]=id_loc[toconvert[i]];
            return toconvert;
        }
        public ArrayList<Move> solution(int[] locs) {
            if (locs.length!=wcnt)
                throw new RuntimeException("Invalid input: "+Arrays.toString(locs));
            return solution(code(locs));
        }
        public ArrayList<Move> solution(int code) {
            if (data[code]==-1)
                return null; //perm never reached (can happen if all perms are restricted to being even)
            ArrayList<Move> out=new ArrayList<>();
            while (true) {
                Move mv=get_move(code).inv();
                if (mv.shift==0)
                    break;
                out.add(mv);
                code= (int)(data[code]%permsAmt);
            }
            return out;
        }
    }
    private static class Move {
        boolean horz;
        int coord, shift;
        public Move(boolean horz, int coord, int shift) {
            this.horz=horz;
            this.coord=coord;
            this.shift=shift;
        }
        public Move transd(int tr, int tc) {
            return new Move(horz,coord+(horz?tr:tc),shift);
        }
        public Move inv() {
            return new Move(horz,coord,-shift);
        }
        public static ArrayList<Move> inv(ArrayList<Move> moves) {
            ArrayList<Move> out=new ArrayList<>();
            for (int i=moves.size()-1; i>-1; i--)
                out.add(moves.get(i).inv());
            return out;
        }
        public String toString() {
            return (horz?"R":"C")+" "+coord+" "+shift;
        }
    }
}
