import java.util.*;
public class LoopoverBruteForce {
    private static int[][] binnedCodes(Tree t, int mind) {
        int[][] codes=new int[t.maxdepth()+1][];
        for (int d=mind; d<=t.maxdepth(); d++) {
            int[] a=new int[t.nperms()];
            int sz=0;
            for (int c=0; c<t.nperms(); c++)
                if (t.depth(c)==d) {
                    a[sz]=c;
                    sz++;
                }
            codes[d]=new int[sz];
            System.arraycopy(a,0,codes[d],0,sz);
        }
        return codes;
    }
    private static int[][] scrambleActions(Tree t, int[][] codes, int mind) {
        int[][] scrambleActions=new int[t.nperms()][];
        for (int d=t.maxdepth(); d>=mind; d--)
            for (int c:codes[d])
                scrambleActions[c]=t.scrambleAction(c);
        return scrambleActions;
    }
    private static void move(int R, int C, int[] perm, int[] mv) {
        if(mv[0]==0) {
            int[] tmp=new int[C];
            for (int i=0; i<C; i++)
                tmp[i]=perm[mv[1]*C+i];
            for (int i=0; i<C; i++)
                perm[mv[1]*C+mod(i+mv[2],C)]=tmp[i];
        }
        else {
            int[] tmp=new int[R];
            for (int i=0; i<R; i++)
                tmp[i]=perm[i*C+mv[1]];
            for (int i=0; i<R; i++)
                perm[mod(i+mv[2],R)*C+mv[1]]=tmp[i];
        }
    }
    private static int transloc(int R, int C, int loc, int tr, int tc) {
        return mod(loc/C+tr,R)*C+mod(loc%C+tc,C);
    }
    private static String str(int R, int C, int[] scramble) {
        int[] perm=new int[R*C];
        for (int i=0; i<R*C; i++)
            perm[scramble[i]]=i;
        StringBuilder str=new StringBuilder();
        for (int i=0; i<R; i++) {
            for (int j=0; j<C; j++)
                str.append(String.format("%3d",perm[i*C+j]));
            str.append("\n");
        }
        return str.toString();
    }
    private static String permStr(int R, int C, int[] perm) {
        StringBuilder str=new StringBuilder();
        for (int i=0; i<R; i++) {
            for (int j=0; j<C; j++)
                str.append(String.format("%3d",perm[i*C+j]));
            str.append("\n");
        }
        return str.toString();
    }
    private static void improve(int R, int C, int[] wr0, int[] wc0, int[] wr1, int[] wc1, int depth, boolean check, boolean show) {
        /*
        creates two BFS trees for solving two subsets of the RxC loopover,
            which gives every RxC loopover permutation an upper bound on the # of moves it takes to solve it,
            then takes every permutation with an upper bound >=depth and solves a translated version of it to obtain a bound <depth
            (exploiting translational symmetry of loopover)
        */
        /*
        set check to true if you want the program to check for correctness, false otherwise
        set show to true if you want the program to show each scramble it tries
         */
        long st=System.currentTimeMillis();
        Tree t0=new Tree(R,C,new int[0], new int[0], wr0, wc0),
                t1=new Tree(R,C,wr0,wc0,wr1,wc1);
        System.out.println("bfs time="+(System.currentTimeMillis()-st));
        //improve depth of all scrambles with (their naive # mvs to solve)>=depth
        st=System.currentTimeMillis();
        int mind0=depth-t1.maxdepth(), mind1=depth-t0.maxdepth();
        int[][] codes0=binnedCodes(t0,mind0),
                codes1=binnedCodes(t1,mind1);
        int[][] sa0=scrambleActions(t0,codes0,mind0),
                sa1=scrambleActions(t1,codes1,mind1);
        int[][] solve0=new int[t0.nperms()][];
        long tot=0;
        for (int d0=t0.maxdepth(); d0>=mind0; d0--)
            for (int d1=t1.maxdepth(); d1>=depth-d0; d1--)
                tot+=(long)codes0[d0].length*codes1[d1].length;
        System.out.println("tot="+tot);
        int[][] transloc=new int[R*C][R*C];
        for (int ti=0; ti<R*C; ti++)
            for (int l=0; l<R*C; l++)
                transloc[ti][l]=transloc(R,C,l,ti/C,ti%C);
        int[] inv_ti=new int[R*C];
        for (int ti=0; ti<R*C; ti++)
            inv_ti[ti]=mod(-(ti/C),R)*C+mod(-(ti%C),C);
        System.out.println("initialization time="+(System.currentTimeMillis()-st));
        long cnt=0;
        double mark=1000_000;
        int maxd=0;
        String form="%20d%20d%n";
        System.out.printf("%20s%20s%n","# improved","time");
        st=System.currentTimeMillis();
        for (int d0=mind0; d0<=t0.maxdepth(); d0++)
            for (int d1=depth-d0; d1<=t1.maxdepth(); d1++)
                for (int c0:codes0[d0])
                    for (int c1:codes1[d1]) {
                        int[] scramble=new int[R*C];
                        for (int i=0; i<R*C; i++)
                            scramble[i]=sa0[c0][sa1[c1][i]];
                        if (show) {
                            System.out.print("d0=" + d0 + ",d1=" + d1 + "\n" + str(R, C, scramble));
                            System.out.println("mvs0=" + t0.bwd_mvids(c0) + ",mvs1=" + t1.bwd_mvids(c1));
                        }
                        int bestd=Integer.MAX_VALUE;
                        for (int ti=1; ti<R*C; ti++) {
                            /*
                            solving scramble with Tree t but with the wanted blocks translated by (tr,tc)
                                is the same as solving tscr with t normally, then translating the resulting moves by (tr,tc)
                                where tscr is defined as tscr[i]=transloc(R,C,scramble[transloc(R,C,i,tr,tc)],-tr,-tc)
                                and transloc(R,C,l,tr,tc) transforms location l by +tr rows and +tc columns
                                    the location l refers to row # l/C, column # l%C
                            NOTE: do not actually create array tscr; only refer to it implicitly when constructing subscr0
                                this will reduce running time
                             */
                            int tr=ti/C, tc=ti%C;
                            int totd=0;
                            int[] subscr0=new int[t0.wcnt];
                            for (int i=0; i<t0.wcnt; i++)
                                subscr0[i]=transloc[inv_ti[ti]][scramble[transloc[ti][t0.id_wloc[i]]]];
                            int code0=t0.subscramble_code(subscr0), code1=-1;
                            boolean skip=false;
                            if (t0.depth(code0)+t1.maxdepth()<depth) {
                                totd = depth - 1;
                                skip=true;
                            }
                            else {
                                if (solve0[code0] == null)
                                    solve0[code0]=t0.solveAction(code0);
                                //now tscr[i]=solve0[code][transloc(R,C,scramble[transloc(R,C,i,tr,tc)],-tr,-tc)];
                                //again, do not create tscr; only refer to it implicitly when constructing subscr1
                                totd+=t0.depth(code0);
                                int[] subscr1=new int[t1.wcnt];
                                for (int i=0; i<t1.wcnt; i++)
                                    subscr1[i]=solve0[code0][transloc[inv_ti[ti]][scramble[transloc[ti][t1.id_wloc[i]]]]];
                                code1=t1.subscramble_code(subscr1);
                                totd+=t1.depth(code1);
                            }
                            if (check && totd<depth) {
                                if (show)
                                    System.out.println("translation=("+tr+","+tc+")");
                                List<int[]> scrA=t0.scrambleMvs(code0), solveA=new ArrayList<>();
                                int[] perm=new int[R*C];
                                for (int i=0; i<R*C; i++)
                                    perm[scramble[i]]=i;
                                for (int i=scrA.size()-1; i>-1; i--) {
                                    int[] mv=inv(scrA.get(i));
                                    int[] tmv=mv[0]==0?new int[] {0,mod(mv[1]+tr,R),mv[2]}:
                                            new int[] {1,mod(mv[1]+tc,C),mv[2]};
                                    move(R, C, perm, tmv);
                                    solveA.add(tmv);
                                }
                                int[] tscramble=new int[R*C];
                                for (int i=0; i<R*C; i++)
                                    tscramble[perm[i]]=i;
                                boolean good=true;
                                for (int i=0; i<R*C; i++)
                                    if (t0.soonLocked(transloc(R,C,i,-tr,-tc)) && tscramble[i]!=i) {
                                        good=false;
                                        break;
                                    }
                                if (!good || show) {
                                    System.out.print((good?"":"NOT SOLVED: \n")+"mvs for solving 1st block=");
                                    for (int[] mv:solveA)
                                        System.out.print(Arrays.toString(mv)+" ");
                                    System.out.println("\n"+permStr(R, C, perm));
                                    if (!show)
                                        System.out.println("translation=("+tr+","+tc+")");
                                    if (!good)
                                        return;
                                }
                                if (!skip) {
                                    List<int[]> scrB = t1.scrambleMvs(code1), solveB=new ArrayList<>();
                                    for (int i = scrB.size() - 1; i > -1; i--) {
                                        int[] mv = inv(scrB.get(i));
                                        int[] tmv = mv[0] == 0 ? new int[]{0, mod(mv[1] + tr, R), mv[2]} :
                                                new int[]{1, mod(mv[1] + tc, C), mv[2]};
                                        move(R, C, perm, tmv);
                                        solveB.add(tmv);
                                    }
                                    boolean solved = true;
                                    for (int i = 0; i < R * C; i++)
                                        if (perm[i] != i) {
                                            solved = false;
                                            break;
                                        }
                                    if (!solved || show) {
                                        if (!solved)
                                            System.out.println("NOT SOLVED");
                                        if (!show) {
                                            System.out.print("mvs for solving 1st block=");
                                            for (int[] mv : solveA)
                                                System.out.print(Arrays.toString(mv) + " ");
                                            System.out.println();
                                        }
                                        System.out.print("mvs for solving 2nd block=");
                                        for (int[] mv:solveB)
                                            System.out.print(Arrays.toString(mv)+" ");
                                        System.out.println("\n"+permStr(R, C, perm));
                                        if (!show)
                                            System.out.println("translation=("+tr+","+tc+")");
                                        if (!solved)
                                            return;
                                    }
                                }
                            }
                            bestd=Math.min(bestd,totd);
                            if (bestd<depth)
                                break;
                        }
                        if (bestd>=depth) {
                            System.out.println("NOT IMPROVED");
                            System.out.print("d0=" + d0 + ",d1=" + d1 + "\n" + str(R, C, scramble));
                            System.out.println("scramble:");
                            List<int[]> s1=t1.scrambleMvs(c1);
                            for (int[] mv:s1)
                                System.out.print(" "+Arrays.toString(mv));
                            System.out.println();
                            List<int[]> s0=t0.scrambleMvs(c0);
                            for (int[] mv:s0)
                                System.out.print(" "+Arrays.toString(mv));
                            System.out.println();
                            System.out.println("[0, x, y] means move row x right y units (left if y is negative)");
                            System.out.println("[1, x, y] means move column x down y units (up if y is negative)");
                            return;
                        }
                        maxd=Math.max(maxd,bestd);
                        cnt++;
                        if (cnt>=mark) {
                            System.out.printf(form,cnt,System.currentTimeMillis()-st);
                            mark*=1.5;
                        }
                    }
        System.out.println("improvement time="+(System.currentTimeMillis()-st));
        System.out.println(cnt+" scrambles of depth>="+depth+" improved to <="+maxd);
        System.out.println("check="+check+", show="+show);
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        improve(4,4,
                new int[]{0, 1}, new int[]{0, 1, 2},
                new int[]{2, 3}, new int[]{3},
                22,false,false);
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
    private static class Tree {
        /*
        make BFS tree of RxC loopover with some rows/cols fixed,
            with the goal of expanding the set of solved rows/cols
            rl[r]=true if row r is already fixed
            cl[c]=true if col c is already fixed
            grl[r]=true if row r is not yet fixed but will be after using the BFS tree
            gcl[c]=true if col c is not yet fixed but will be after using the BFS tree
        */
        private int R, C;
        private boolean[] rl, cl, grl, gcl;
        private int[] loc_id, id_floc, id_wloc;
        private int[][] moves;
        private long[] data;
        /*
        data[code]=# representing (depth,mvid,par)
        let scr be the subscramble represented by int code
        depth=depth of scr in BFS
        mvid=id of the move that transformed the parent of scr to scr
        par=parent of scr
         */
        private int nperms, fcnt, wcnt, maxdepth;
        private boolean soonLocked(int i) {
            return grl[i/C] && gcl[i%C];
        }
        private int maxdepth() {
            return maxdepth;
        }
        private int nperms() {
            return nperms;
        }
        private long compressed(int depth, int mvid, int par) {
            return ((long)depth*moves.length+mvid)*nperms+par;
        }
        public int depth(int code) {
            return (int)(data[code]/nperms/moves.length);
        }
        public int mvid(int code) {
            return (int)(data[code]/nperms%moves.length);
        }
        public int par(int code) {
            return (int)(data[code]%nperms);
        }
        public Tree(int R, int C, int[] lr, int[] lc, int[] wr, int[] wc) {
            this.R=R;
            this.C=C;
            rl=new boolean[R];
            cl=new boolean[C];
            for (int r:lr)
                rl[r]=true;
            for (int c:lc)
                cl[c]=true;
            int nlr=0, nlc=0;
            for (boolean b:rl) if (b) nlr++;
            for (boolean b:cl) if (b) nlc++;
            grl=rl.clone();
            gcl=cl.clone();
            for (int r:wr)
                grl[r]=true;
            for (int c:wc)
                gcl[c]=true;
            int nglr=0, nglc=0;
            for (boolean b:grl) if (b) nglr++;
            for (boolean b:gcl) if (b) nglc++;
            fcnt=R*C-nlr*nlc;
            loc_id=new int[R*C];
            id_floc =new int[fcnt];
            for (int i=0, id=0; i<R*C; i++) {
                int r=i/C, c=i%C;
                if (rl[r] && cl[c])
                    loc_id[i]=-1;
                else {
                    loc_id[i]=id;
                    id_floc[id]=i;
                    id++;
                }
            }
            wcnt=nglr*nglc-nlr*nlc;
            id_wloc=new int[wcnt];
            for (int i=0, id=0; i<R*C; i++) {
                int r=i/C, c=i%C;
                if (grl[r] && gcl[c] && !(rl[r] && cl[c])) {
                    id_wloc[id]=i;
                    id++;
                }
            }
            moves=new int[2*(R-nlr+C-nlc)][];
            for (int type=0, id=0; type<2; type++) {
                for (int coord=0; coord<(type==0?R:C); coord++)
                    if (!(type==0?rl:cl)[coord])
                        for (int shift=-1; shift<=1; shift+=2) {
                            moves[id]=new int[] {type,coord,shift};
                            id++;
                        }
            }
            for (int m=0; m<moves.length; m++)
                System.out.println(m+":"+Arrays.toString(moves[m]));
            nperms=1;
            for (int i=fcnt; i>fcnt-wcnt; i--)
                nperms*=i;
            System.out.println(R+" "+C+" "
                    +Arrays.toString(lr)+" "+Arrays.toString(lc)+" "
                    +Arrays.toString(wr)+" "+Arrays.toString(wc));
            System.out.println(nperms);
            data=new long[nperms];
            Arrays.fill(data,-1);
            int initcode=subscramble_code(id_wloc);
            System.out.println(Arrays.toString(id_wloc));
            data[initcode]=compressed(0,0,0);
            maxdepth =0;
            int[] front={initcode};
            int reached=1;
            while (true) {
                int[] nf=new int[nperms];
                int sz=0;
                for (int c:front) {
                    int[] subscramble=code_subscramble(c);
                    for (int m=0; m<moves.length; m++) {
                        int nc=//subscramble_code(moved(subscramble,moves[m]));
                                moved_code(subscramble,moves[m]);
                        if (data[nc]==-1) {
                            data[nc]=compressed(depth(c)+1,m,c);
                            nf[sz]=nc;
                            sz++;
                            reached++;
                        }
                    }
                }
                if (sz==0)
                    break;
                maxdepth++;
                front=new int[sz];
                System.arraycopy(nf,0,front,0,sz);
                System.out.println(maxdepth +":"+sz);
            }
            if (reached<nperms)
                System.out.println("!!!ONLY REACHED "+reached+"/"+nperms);
            System.out.println("maxdepth="+ maxdepth);
        }
        private int moved_code(int[] subscramble, int[] mv) {
            int[] loc=new int[fcnt];
            for (int i=0; i<fcnt; i++)
                loc[i]=i;
            int[] perm=loc.clone();
            int out=0;
            for (int b=fcnt; b>fcnt-wcnt; b--) {
                out*=b;
                int piece=subscramble[b-1-(fcnt-wcnt)],
                        r=piece/C, c=piece%C;
                int v=loc_id[
                        mv[0]==0 && r==mv[1]?
                                (r*C+mod(c+mv[2],C)):
                                mv[0]==1 && c==mv[1]?
                                        (mod(r+mv[2],R)*C+c):
                                        piece], l=loc[v];
                int ov=perm[b-1];
                out+=l;
                loc[ov]=l;
                perm[l]=ov;
            }
            return out;
        }
        private int[] moved(int[] subscramble, int[] mv) {
            int[] out=subscramble.clone();
            if (mv[0]==0)
                for (int i=0; i<subscramble.length; i++) {
                    int r=subscramble[i]/C, c=subscramble[i]%C;
                    if (r==mv[1])
                        out[i]=r*C+mod(c+mv[2],C);
                }
            else
                for (int i=0; i<subscramble.length; i++) {
                    int r=subscramble[i]/C, c=subscramble[i]%C;
                    if (c==mv[1])
                        out[i]=mod(r+mv[2],R)*C+c;
                }
            return out;
        }
        private int subscramble_code(int[] subscramble) {
            int[] loc=new int[fcnt];
            for (int i=0; i<fcnt; i++)
                loc[i]=i;
            int[] perm=loc.clone();
            int out=0;
            for (int b=fcnt; b>fcnt-wcnt; b--) {
                out*=b;
                int v=loc_id[subscramble[b-1-(fcnt-wcnt)]], l=loc[v];
                int ov=perm[b-1];
                out+=l;
                loc[ov]=l;
                perm[l]=ov;
            }
            return out;
        }
        private int[] code_subscramble(int code) {
            int pow=1;
            for (int i=fcnt-wcnt+1; i<fcnt; i++)
                pow*=i;
            int[] perm=new int[fcnt];
            for (int i=0; i<fcnt; i++)
                perm[i]=i;
            for (int id=fcnt-1; id>fcnt-1-wcnt; id--) {
                int idx=code/pow;
                int tmp=perm[id];
                perm[id]=perm[idx];
                perm[idx]=tmp;
                code=code%pow;
                if (id!=0)
                    pow/=id;
            }
            int[] out=new int[wcnt];
            for (int i=0; i<wcnt; i++)
                out[i]=id_floc[perm[i+fcnt-wcnt]];
            return out;
        }
        public int[] solveAction(int code) {
            if (depth(code)==-1)
                throw new RuntimeException();
            int[] out=new int[R*C];
            for (int i=0; i<R*C; i++)
                out[i]=i;
            for (int c=code; depth(c)>0; c=par(c))
                out=moved(out,inv(moves[mvid(c)]));
            return out;
        }
        public int[] scrambleAction(int code) {
            int[] tmp=solveAction(code);
            int[] out=new int[R*C];
            for (int i=0; i<R*C; i++)
                out[tmp[i]]=i;
            return out;
        }
        public List<Integer> bwd_mvids(int code) {
            List<Integer> out=new ArrayList<>();
            for (int c=code; depth(c)>0; c=par(c))
                out.add(mvid(c));
            return out;
        }
        public List<int[]> scrambleMvs(int code) {
            List<Integer> ids=bwd_mvids(code);
            List<int[]> out=new ArrayList<>();
            for (int i=ids.size()-1; i>-1; i--)
                out.add(moves[ids.get(i)].clone());
            return out;
        }
    }
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static int[] inv(int[] mv) {
        return new int[] {mv[0],mv[1],-mv[2]};
    }
}
