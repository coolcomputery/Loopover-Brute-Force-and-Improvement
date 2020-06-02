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
        System.out.println("memoizing "+t.str);
        int[][] scrambleActions=new int[t.nperms()][];
        for (int d=t.maxdepth(); d>=mind; d--) {
            System.out.println("starting depth "+d);
            long st=System.currentTimeMillis();
            for (int c : codes[d])
                scrambleActions[c]=t.scrambleAction(c);
            System.out.println("done in time="+(System.currentTimeMillis()-st));
        }
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
    private static String str(int[][] aa) {
        StringBuilder str=new StringBuilder();
        for (int i=0; i<aa.length; i++)
            str.append(i==0?"":", ").append(Arrays.toString(aa[i]));
        return str.toString();
    }
    private static String str(Collection<int[]> aa) {
        StringBuilder str=new StringBuilder();
        boolean first=true;
        for (int[] a:aa) {
            if (first)
                first=false;
            else
                str.append(",");
            str.append(Arrays.toString(a));
        }
        return str.toString();
    }
    private static String str(int R, int C, int[] scramble) {
        int[] perm=new int[R*C];
        for (int i=0; i<R*C; i++)
            perm[scramble[i]]=i;
        return permStr(R,C,perm);
    }
    private static String permStr(int R, int C, int[] perm) {
        StringBuilder str=new StringBuilder();
        for (int i=0; i<R; i++) {
            for (int j=0; j<C; j++)
                str.append(String.format("%3s",(char)('A'+perm[i*C+j])));
            str.append("\n");
        }
        return str.toString();
    }
    private static int transloc(int R, int C, int loc, int tr, int tc) {
        return mod(loc/C+tr,R)*C+mod(loc%C+tc,C);
    }
    private static int[] trnsl_mv(int R, int C, int[] mv, int tr, int tc) {
        return mv[0]==0?
                new int[]{0, mod(mv[1]+tr, R), mv[2]} :
                new int[]{1, mod(mv[1]+tc, C), mv[2]};
    }
    private static int[] flipr_mv(int R, int[] mv) {
        return mv[0]==0?
                new int[] {mv[0],mod(R-1-mv[1], R),mv[2]}:
                new int[] {mv[0],mv[1],mod(-mv[2],R)};
    }
    private static int[] flipc_mv(int C, int[] mv) {
        return mv[0]==0?
                new int[] {mv[0],mv[1],mod(-mv[2],C)}:
                new int[] {mv[0],mod(C-1-mv[1],C),mv[2]};
    }
    private static int[] transf_mv(int R, int C, int[] mv,
                                   int flipr, int flipc, int flipd,
                                   int tr, int tc) {
        int[] tmv=mv.clone();
        if (flipr==1)
            tmv=flipr_mv(R, tmv);
        if (flipc==1)
            tmv=flipc_mv(C, tmv);
        if (flipd==1)
            tmv=flipd_mv(tmv);
        return trnsl_mv(R, C, tmv, tr, tc);
    }
    private static int[] flipd_mv(int[] mv) {
        return new int[] {1-mv[0],mv[1],mv[2]};
    }
    private static void improveComplete(int R, int C,
                                        int[] lr0, int[] lc0,
                                        int depth, boolean check, boolean show, boolean store_scrambleActions) {
        /*
        does a 0x0 -> {lr0}x{lc0} -> NxN blok-building algorithm,
            then takes all scrambles of NxN Loopover that result in a solution of length >=depth
            and tries doing block-building but in a transformed fashion to take advantage of symmetry of Loopover
                (start block at different location, build in other directions, etc.)
         */
        /*
        set check to true if you want the program to check for correctness, false otherwise
        set show to true if you want the program to show each scramble it tries
        set store_scrambleActions to true if you want to store each scramble as a permutation
            instead of having to always reconstruct it from a BFS tree
         */
        long st=System.currentTimeMillis();
        boolean[] rl=new boolean[R], cl=new boolean[C];
        for (int r:lr0)
            rl[r]=true;
        for (int c:lc0)
            cl[c]=true;
        int nwr=0, nwc=0;
        for (int r=0; r<R; r++)
            if (!rl[r])
                nwr++;
        for (int c=0; c<C; c++)
            if (!cl[c])
                nwc++;
        int[] wr=new int[nwr], wc=new int[nwc];
        for (int i=0, r=0; r<R; r++)
            if (!rl[r]) {
                wr[i]=r;
                i++;
            }
        for (int i=0, c=0; c<C; c++)
            if (!cl[c]) {
                wc[i]=c;
                i++;
            }
        Tree t0=new Tree(R,C,new int[0], new int[0], lr0, lc0),
                t1=new Tree(R,C,lr0,lc0,wr,wc);
        System.out.println("bfs time="+(System.currentTimeMillis()-st));
        System.out.println("depth to improve="+depth);
        st=System.currentTimeMillis();
        int mind0=depth-t1.maxdepth(), mind1=depth-t0.maxdepth();
        int[][] codes0=binnedCodes(t0,mind0),
                codes1=binnedCodes(t1,mind1);
        int[][] sa1=scrambleActions(t1,codes1,mind1);
        int[][] solve0=new int[t0.nperms()][];
        boolean flip=R==C;
        int T=flip?8*R*C:4*R*C;
        int[][] transf=new int[T][R*C];
        for (int ti=0; ti<T; ti++)
            for (int l=0; l<R*C; l++) {
                int nl=(ti&1)==0?l:(R-1-l/C)*C+l%C; //reflect over horizontal center
                nl=(ti&2)==0?nl:nl/C*C+(C-1-nl%C); //reflect over vertical center
                if (flip) {
                    nl=(ti&4)==0?nl:(nl%C)*C+(nl/C); //flip row and col coords
                    int tri=ti / 8;
                    transf[ti][l]=transloc(R, C, nl, tri / C, tri % C);
                }
                else {
                    int tri=ti / 4;
                    transf[ti][l]=transloc(R, C, nl, tri / C, tri % C);
                }
            }
        int[][] inv_transf=new int[T][R*C];
        for (int t=0; t<T; t++) {
            for (int l=0; l<R*C; l++)
                inv_transf[t][transf[t][l]]=l;
        }
        int[] tarr=new int[T*R*C], invtarr=new int[T*R*C];
        //converting 2D arrays to 1D arrays doesn't seem to improve speed by much
        for (int t=0; t<T; t++)
            for (int l=0; l<R*C; l++) {
                tarr[t*R*C+l]=transf[t][l];
                invtarr[t*R*C+l]=inv_transf[t][l];
            }
        long tot=0;
        for (int d0=t0.maxdepth(); d0>=mind0; d0--)
            for (int d1=t1.maxdepth(); d1>=depth-d0; d1--)
                tot+=(long)codes0[d0].length*codes1[d1].length;
        long[] s1suff=new long[codes1.length];
        for (int d=s1suff.length-1; d>=mind1; d--)
            s1suff[d]=codes1[d].length+(d<s1suff.length-1?s1suff[d+1]:0);
        System.out.println("tot="+tot);
        System.out.println("initialization time="+(System.currentTimeMillis()-st));
        long totcnt=0;
        int maxd=0;
        String form="%40d%40s%20d%n";
        System.out.printf("%20s%20s%n","# improved","time");
        st=System.currentTimeMillis();
        for (int d0=mind0; d0<=t0.maxdepth(); d0++) {
            System.out.println("starting d0="+d0+" (# scrambles="+((long)codes0[d0].length*s1suff[depth-d0])+")");
            System.out.printf("%40s%40s%20s%n", "idx of 1st-stage scramble of depth d0 ", "# scrambles processed (cumulative)", "time");
            long t01cnt=0;
            double checkpt=0, mark=1000_000;
            for (int idx=0; idx<codes0[d0].length; idx++) {
                int c0=codes0[d0][idx];
                int[] scra0=t0.scrambleAction(c0);
                for (int d1=depth-d0; d1 <= t1.maxdepth(); d1++) {
                    for (int c1 : codes1[d1]) {
                        int[] scra1=sa1[c1];
                        int bestd=depth;
                        for (int ti=1; ti<T; ti++) {
                            /*
                            solving scramble with Tree t but with the wanted blocks transformed from the original wanted blocks
                            is the same as solving the original wanted blocks of a special scramble, tscr[], is defined as tscr[i]=T^(-1)[ scramble[T[i]] ]
                            where T is the transformation and T^-1 is the negative transformation
                            NOTE: do not actually create array tscr; only refer to it implicitly when constructing subscr0 and subscr1;
                                this will reduce running time
                             */
                            int totd=0;
                            int[] subscr0=new int[t0.wcnt]; //subscr0[i]=tscr[t0.id_wloc[i]]
                            for (int i=0; i<t0.wcnt; i++)
                                subscr0[i]=invtarr[ti*R*C+scra0[scra1[tarr[ti*R*C+t0.id_wloc[i]]]]];
                            int code0=t0.subscramble_code(subscr0), code1=-1;
                            boolean skip=false;
                            if (t0.depth(code0)+t1.maxdepth()<depth) {
                                totd=depth-1;
                                skip=true;
                            }
                            else {
                                if (solve0[code0]==null)
                                    solve0[code0]=t0.solveAction(code0);
                                //now tscr'[i]=solve0[code][tscr[i]] (tscr'=tscr put under the solve0[code] transformation)
                                //again, do not create tscr; only refer to it implicitly when constructing subscr1
                                totd+=t0.depth(code0);
                                int[] subscr1=new int[t1.wcnt];
                                for (int i=0; i<t1.wcnt; i++)
                                    subscr1[i]=solve0[code0][invtarr[ti*R*C+scra0[scra1[tarr[ti*R*C+t1.id_wloc[i]]]]]];
                                code1=t1.subscramble_code(subscr1);
                                totd+=t1.depth(code1);
                            }
                            if (check) {
                                int[] scramble=new int[R*C];
                                for (int i=0; i<R*C; i++)
                                    scramble[i]=scra0[scra1[i]];
                                int flipr=ti&1, flipc=(ti&2)==0?0:1;
                                int flipd, tri;
                                if (flip) {
                                    flipd=(ti&4)==0?0:1;
                                    tri=ti/8;
                                }
                                else {
                                    flipd=0;
                                    tri=ti/4;
                                }
                                int tr=tri/C, tc=tri%C;
                                List<int[]> scrA=t0.scrambleMvs(code0), scrB,
                                        solveA=new ArrayList<>(), solveB=null;
                                int[] perm=new int[R*C];
                                for (int i=0; i<R*C; i++)
                                    perm[scramble[i]]=i;
                                for (int i=scrA.size()-1; i>-1; i--) {
                                    int[] tmv=transf_mv(R,C,inv(scrA.get(i)),flipr,flipc,flipd,tr,tc);
                                    solveA.add(tmv);
                                    move(R, C, perm, tmv);
                                }
                                boolean good=true;
                                for (int i=0; i<R*C; i++)
                                    if (t0.postSolved(inv_transf[ti][i]) && perm[i]!=i) {
                                        good=false;
                                        break;
                                    }
                                if (!skip && good) {
                                    scrB=t1.scrambleMvs(code1);
                                    solveB=new ArrayList<>();
                                    for (int i=scrB.size()-1; i>-1; i--) {
                                        int[] tmv=transf_mv(R,C,inv(scrB.get(i)),flipr,flipc,flipd,tr,tc);
                                        move(R, C, perm, tmv);
                                        solveB.add(tmv);
                                    }
                                    for (int i=0; i<R*C; i++)
                                        if (t1.postSolved(inv_transf[ti][i]) && perm[i]!=i) {
                                            good=false;
                                            break;
                                        }
                                }
                                if (!good || show) {
                                    if (!good)
                                        System.out.println("NOT SOLVED");
                                    System.out.printf("transf=%d,%d,%d,%d,%d%n", flipr, flipc, flipd, tr, tc);
                                    System.out.println("original depths: d0="+d0+", d1="+d1);
                                    System.out.println("mvs for solving 1st block="+str(solveA));
                                    if (!skip)
                                        System.out.println("mvs for solving 2nd block="+str(solveB));
                                    int[] scr=new int[R*C];
                                    for (int i=0; i<R*C; i++)
                                        scr[i]=inv_transf[ti][scramble[transf[ti][i]]];
                                    System.out.println("transformed scramble:\n"+str(R, C, scr));
                                    System.out.print("result=\n"+permStr(R, C, perm));
                                    if (!good) {
                                        System.out.print("orig. scramble: d0="+d0+",d1="+d1+"\n"+str(R, C, scramble));
                                        return;
                                    }
                                }
                            }
                            bestd=Math.min(bestd, totd);
                            if (bestd<depth) break;
                        }
                        if (bestd>=depth || show) {
                            if (bestd>=depth)
                                System.out.println("NOT IMPROVED");
                            int[] scramble=new int[R*C];
                            for (int i=0; i<R*C; i++)
                                scramble[i]=scra0[scra1[i]];
                            System.out.print("orig. scramble: d0="+d0+",d1="+d1+"\n"+str(R, C, scramble));
                            System.out.println("scramble moves:"+str(t1.scrambleMvs(c1))
                                    +"\n+"+str(t0.scrambleMvs(c0)));
                            if (bestd>=depth) {
                                System.out.println("[0, x, y] means move row x right y units (left if y is negative)");
                                System.out.println("[1, x, y] means move column x down y units (up if y is negative)");
                                return;
                            }
                        }
                        maxd=Math.max(maxd, bestd);
                        totcnt++;
                        t01cnt++;
                        if (t01cnt>=mark) {
                            System.out.printf(form, idx, t01cnt+" ("+totcnt+")", System.currentTimeMillis()-st);
                            checkpt++;
                            mark=1000_000*Math.exp(Math.sqrt(checkpt));
                        }
                    }
                }
            }
        }
        System.out.println("improvement time="+(System.currentTimeMillis()-st));
        System.out.println(totcnt+" scrambles of depth>="+depth+" improved to <="+maxd);
        System.out.println("check="+check+", show="+show+", store_scrambleActions="+store_scrambleActions);
    }

    private static int[] union(int M, int[] a, int[] b) {
        boolean[] e=new boolean[M];
        for (int i:a)
            e[i]=true;
        for (int i:b)
            e[i]=true;
        int amt=0;
        for (boolean i:e)
            if (i)
                amt++;
        int[] out=new int[amt];
        for (int i=0, v=0; v<M; v++)
            if (e[v]) {
                out[i]=v;
                i++;
            }
        return out;
    }
    private static void improve(int R, int C,
                                int[] lr0, int[] lc0, int[] wr0, int[] wc0, int[] wr1, int[] wc1,
                                int depth, boolean check, boolean show, boolean store_scrambleActions) {
        //{lr0}x{lc0}->{lr0 union wr0}x{lc0 union wc0}->{lr0 union wr0 union wr1}x{lc0 union wc0 union wc1}
        long st=System.currentTimeMillis();
        boolean[] rl=new boolean[R], cl=new boolean[C];
        for (int r:lr0)
            rl[r]=true;
        for (int c:lc0)
            cl[c]=true;
        int[] lr1=union(R,lr0,wr0), lc1=union(C,lc0,wc0);
        Tree t0=new Tree(R,C,lr0,lc0,wr0,wc0),
                t1=new Tree(R,C,lr1,lc1,wr1,wc1);
        System.out.println("bfs time="+(System.currentTimeMillis()-st));
        System.out.println("depth to improve="+depth);
        st=System.currentTimeMillis();
        int mind0=depth-t1.maxdepth(), mind1=depth-t0.maxdepth();
        int[][] codes0=binnedCodes(t0,mind0),
                codes1=binnedCodes(t1,mind1);
        int[][] sa1=scrambleActions(t1,codes1,mind1);
        int[][] solve0=new int[t0.nperms()][];
        List<int[][]> prefixes=new ArrayList<>();
        for (int c=0; c<2*R*C; c++) {
            int[] m=t0.code_move(c);
            if (m[2]==0
                    || (m[0]==0 && rl[m[1]])
                    || (m[0]==1 && cl[m[1]]))
                continue;
            prefixes.add(new int[][]{m});
        }
        int[] prefixCosts=new int[prefixes.size()];
        for (int i=0; i<prefixes.size(); i++) {
            prefixCosts[i]=0;
            for (int[] p:prefixes.get(i)) {
                int l=p[0]==0?R:C, d=mod(p[2],l);
                prefixCosts[i]+=Math.min(d,Math.abs(d-l));
            }
            System.out.println(str(prefixes.get(i))+" cost="+prefixCosts[i]);
        }
        int[][] prefixActions=new int[prefixes.size()][];
        for (int pi=0; pi<prefixes.size(); pi++) {
            int[] act=new int[R*C];
            for (int i=0; i<R*C; i++)
                act[i]=i;
            for (int[] m:prefixes.get(pi))
                act=t0.moved(act,t0.move_code(m));
            prefixActions[pi]=act;
        }
        long tot=0;
        for (int d0=t0.maxdepth(); d0>=mind0; d0--)
            for (int d1=t1.maxdepth(); d1>=depth-d0; d1--)
                tot += (long) codes0[d0].length * codes1[d1].length;
        long[] s1suff=new long[codes1.length];
        for (int d=s1suff.length-1; d>=mind1; d--)
            s1suff[d]=codes1[d].length+(d<s1suff.length-1?s1suff[d+1]:0);
        System.out.println("tot="+tot);
        System.out.println("initialization time="+(System.currentTimeMillis()-st));
        long totcnt=0;
        int maxd=0;
        String form="%40d%40s%20d%n";
        st=System.currentTimeMillis();
        for (int d0=mind0; d0<=t0.maxdepth(); d0++) {
            System.out.println("starting d0="+d0+" (# t0-t1 scrambles="+((long)codes0[d0].length*s1suff[depth-d0])+")");
            System.out.printf("%40s%40s%20s%n", "idx of 1st-stage scramble of depth d0 ", "# scrambles processed (cumulative)", "time");
            long t01cnt=0;
            double checkpt=0, mark=1000_000;
            for (int idx=0; idx<codes0[d0].length; idx++) {
                int c0=codes0[d0][idx];
                int[] scra0 = t0.scrambleAction(c0);
                for (int d1 = depth - d0; d1 <= t1.maxdepth(); d1++) {
                    for (int c1 : codes1[d1]) {
                        int[] scra1=sa1[c1];
                        //scramble[i]=scra0[scra1[i]]
                        if (show) {
                            int[] scramble = new int[R * C];
                            for (int i = 0; i < R * C; i++)
                                scramble[i] = scra0[scra1[i]];
                            System.out.print("d0=" + d0 + ",d1=" + d1 + "\n" + str(R, C, scramble));
                            System.out.println("scramble=");
                            List<int[]> $0 = t0.scrambleMvs(c0);
                            List<int[]> $1 = t1.scrambleMvs(c1);
                            for (int[] mv : $1)
                                System.out.print(" " + Arrays.toString(mv));
                            System.out.println();
                            for (int[] mv : $0)
                                System.out.print(" " + Arrays.toString(mv));
                            System.out.println();
                        }
                        int bestd = Integer.MAX_VALUE;
                        for (int pi = 0; pi < prefixes.size(); pi++) {
                            int totd = prefixCosts[pi];
                            int[] subscr0 = new int[t0.wcnt];
                            for (int i = 0; i < subscr0.length; i++)
                                subscr0[i] = prefixActions[pi][scra0[scra1[t0.id_wloc[i]]]];//scramble[t0.id_wloc[i]]];
                            int code0 = t0.subscramble_code(subscr0), code1 = -1;
                            boolean skip = false;
                            if (totd + t0.depth(code0) + t1.maxdepth() < depth) {
                                totd = depth - 1;
                                skip = true;
                            } else {
                                if (solve0[code0] == null)
                                    solve0[code0] = t0.solveAction(code0);
                                totd += t0.depth(code0);
                                int[] subscr1 = new int[t1.wcnt];
                                for (int i = 0; i < t1.wcnt; i++)
                                    subscr1[i] = solve0[code0][prefixActions[pi][scra0[scra1[t1.id_wloc[i]]]]];//scramble[t1.id_wloc[i]]]];
                                code1 = t1.subscramble_code(subscr1);
                                totd += t1.depth(code1);
                            }
                            if (check) {
                                int[] scramble = new int[R * C];
                                for (int i = 0; i < R * C; i++)
                                    scramble[i] = scra0[scra1[i]];
                                int[][] prefix = prefixes.get(pi);
                                int[] perm = new int[R * C];
                                for (int i = 0; i < R * C; i++)
                                    perm[scramble[i]] = i;
                                List<int[]> s0 = inv(t0.scrambleMvs(code0));
                                for (int[] p : prefix)
                                    move(R, C, perm, p);
                                for (int[] m : s0)
                                    move(R, C, perm, m);
                                boolean good = true;
                                for (int i = 0; i < R * C; i++)
                                    if (t0.postSolved(i) && perm[i] != i) {
                                        good = false;
                                        break;
                                    }
                                if (!good || show) {
                                    if (!good)
                                        System.out.println("INCORRECT");
                                    System.out.println("orig=\n" + str(R, C, scramble));
                                    System.out.println("prefix=" + str(prefix));
                                    System.out.println("1st block solve=" + str(s0));
                                    System.out.println(permStr(R, C, perm));
                                    if (!good)
                                        return;
                                }
                                if (!skip) {
                                    List<int[]> s1 = inv(t1.scrambleMvs(code1));
                                    for (int[] m : s1)
                                        move(R, C, perm, m);
                                    for (int i = 0; i < R * C; i++)
                                        if (t1.postSolved(i) && perm[i] != i) {
                                            good = false;
                                            break;
                                        }
                                    if (!good || show) {
                                        if (!good)
                                            System.out.println("INCORRECT");
                                        if (!show) {
                                            System.out.println("orig=\n" + str(R, C, scramble));
                                            System.out.println("prefix=" + str(prefix));
                                            System.out.println("1st block solve=" + str(s0));
                                        }
                                        System.out.println("2nd block solve=" + str(s1));
                                        System.out.println(permStr(R, C, perm));
                                        //System.out.println(totd+" "+prefixCosts[pi]+" "+s0.size()+" "+s1.size());
                                        if (!good)
                                            return;
                                    }
                                }
                            }
                            bestd = Math.min(bestd, totd);
                            if (bestd < depth) break;
                        }
                        if (bestd >= depth) {
                            int[] scramble = new int[R * C];
                            for (int i = 0; i < R * C; i++)
                                scramble[i] = scra0[scra1[i]];
                            System.out.println("NOT IMPROVED");
                            System.out.print("d0=" + d0 + ",d1=" + d1 + "\n" + str(R, C, scramble));
                            System.out.println("scramble:");
                            List<int[]> s1 = t1.scrambleMvs(c1);
                            System.out.println(str(s1));
                            List<int[]> s0 = t0.scrambleMvs(c0);
                            System.out.println(str(s0));
                            System.out.println("[0, x, y] means move row x right y units (left if y is negative)");
                            System.out.println("[1, x, y] means move column x down y units (up if y is negative)");
                            return;
                        }
                        maxd = Math.max(maxd, bestd);
                        totcnt++;
                        t01cnt++;
                        if (t01cnt >= mark) {
                            System.out.printf(form, idx, t01cnt+" ("+totcnt+")", System.currentTimeMillis() - st);
                            checkpt++;
                            mark=1000_000*Math.exp(Math.sqrt(checkpt));
                        }
                    }
                }
            }
        }
        System.out.println("improvement time="+(System.currentTimeMillis()-st));
        System.out.println(totcnt+" scrambles of depth>="+depth+" improved to <="+maxd);
        System.out.println("check="+check+", show="+show+", store_scrambleActions="+store_scrambleActions);
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        improveComplete(4,4,new int[] {0,1},new int[] {0,1,2},27,false,false,true);
        //new Tree(3,3,new int[] {},new int[] {},new int[] {0,1,2},new int[] {0,1,2});
        /*new Tree(4,4,new int[] {},new int[] {},new int[] {0,1},new int[] {0,1,2});
        new Tree(4,4,new int[] {0,1},new int[] {0,1,2},new int[] {2,3},new int[] {3});*/
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
    private static class Tree {
        private int R, C, NM;
        private boolean[] rl, cl, grl, gcl;
        private int[] loc_id, id_floc, id_wloc;
        private long[] data;
        private String str;
        /*
        data[code]=# representing (depth,mvid,par)
        let scr be the subscramble represented by int code
        depth=depth of scr in BFS
        mvid=code # of the move that transformed the parent of scr to scr
        par=parent of scr
         */
        private int nperms, fcnt, wcnt, maxdepth;
        private int[][] moved_loc;
        private int[] mvc_inv;
        private boolean postSolved(int i) {
            return grl[i/C] && gcl[i%C];
        }
        private int maxdepth() {
            return maxdepth;
        }
        private int nperms() {
            return nperms;
        }
        private int move_code(int[] mv) {
            if (mv[0]==0)
                return (mod(mv[1],R)*C+mod(mv[2],C))*2;
            else
                return (mod(mv[1],C)*R+mod(mv[2],R))*2+1;
        }
        private int[] code_move(int code) {
            if ((code&1)==0)
                return new int[] {0,code/2/C,code/2%C};
            else
                return new int[] {1,code/2/R,code/2%R};
        }
        private long compressed(int depth, int mvc, int par) {
            return ((long)depth*NM+mvc)*nperms+par;
        }
        public int depth(int code) {
            return (int)(data[code]/nperms/NM);
        }
        public int[] mv(int code) {
            return code_move((int)(data[code]/nperms%NM));
        }
        private int mvc(int code) {
            return (int)(data[code]/nperms%NM);
        }
        public int par(int code) {
            return (int)(data[code]%nperms);
        }
        public Tree(int R, int C, int[] lr, int[] lc, int[] wr, int[] wc) {
            //lr[], lc[]=rows and columns that are not allowed to be moved (tiles whose rows & cols are both locked cannot be moved)
            //wr[], wc[]=new rows and columns s.t. we want to convert every (R,C,lr,lc) Loopover subgroup
            //  to a (R,C,(lr union wr),(lc union wc)) Loopover subgroup
            this.R=R;
            this.C=C;
            NM=2*R*C;
            rl=new boolean[R];
            cl=new boolean[C];
            addb(rl,lr);
            addb(cl,lc);
            int nlr=cnt(rl), nlc=cnt(cl);
            grl=rl.clone();
            gcl=cl.clone();
            addb(grl,wr);
            addb(gcl,wc);
            int nglr=cnt(grl), nglc=cnt(gcl);
            fcnt=R*C-nlr*nlc;
            loc_id=new int[R*C]; //loc_id[l]=id # of free location l, -1 if l is not free
            id_floc =new int[fcnt]; //id_floc[i]=location of i-th free location=loc_id^(-1)[i]
            wcnt=nglr*nglc-nlr*nlc;
            id_wloc=new int[wcnt]; //id_wloc[i]=location of i-th tile we want to solve
            for (int i=0, id=0, wid=0; i<R*C; i++) {
                int r=i/C, c=i%C;
                if (rl[r] && cl[c])
                    loc_id[i]=-1;
                else {
                    loc_id[i]=id;
                    id_floc[id]=i;
                    id++;
                    if (grl[r] && gcl[c]) {
                        id_wloc[wid]=i;
                        wid++;
                    }
                }
            }
            int[] mv_codes=new int[2*(R-nlr+C-nlc)];
            for (int type=0, id=0; type<2; type++) {
                for (int coord=0; coord<(type==0?R:C); coord++)
                    if (!(type==0?rl:cl)[coord])
                        for (int shift=-1; shift<=1; shift+=2) {
                            mv_codes[id]=move_code(new int[] {type,coord,shift});
                            id++;
                        }
            }
            moved_loc=new int[NM][R*C];
            mvc_inv=new int[NM];
            for (int mvc=0; mvc<NM; mvc++) {
                int[] mv=code_move(mvc);
                mvc_inv[mvc]=move_code(inv(mv));
                for (int r=0; r<R; r++)
                    for (int c=0; c<C; c++) {
                        moved_loc[mvc][r*C+c]=
                                mv[0]==0 && r==mv[1]?
                                        (r*C+mod(c+mv[2],C)):
                                        mv[0]==1 && c==mv[1]?
                                                (mod(r+mv[2],R)*C+c):
                                                r*C+c;
                    }
            }
            long n_perms=1;
            for (int i=fcnt; i>fcnt-wcnt; i--)
                n_perms*=i;
            if (n_perms>Integer.MAX_VALUE)
                throw new RuntimeException("Too many permutations.");
            nperms=(int)n_perms;
            str="R="+R+" C="+C
                    +" lr="+Arrays.toString(lr)+" lc="+Arrays.toString(lc)
                    +" wr="+Arrays.toString(wr)+" wc="+Arrays.toString(wc);
            System.out.println(str);
            System.out.println("tot perms="+n_perms);
            data=new long[nperms];
            Arrays.fill(data,-1);
            int initcode=subscramble_code(id_wloc);
            System.out.println("id_wloc="+Arrays.toString(id_wloc));
            data[initcode]=compressed(0,0,0);
            maxdepth=0;
            int[] front={initcode};
            int reached=1;
            while (true) {
                int[] nf=new int[nperms];
                int sz=0;
                for (int c:front) {
                    int[] subscramble=code_subscramble(c);
                    for (int mvc:mv_codes) {
                        int nc=moved_code(subscramble,mvc);
                        if (data[nc]==-1) {
                            data[nc]=compressed(depth(c)+1,mvc,c);
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
            if (reached<n_perms)
                System.out.println("!!!ONLY REACHED "+reached+"/"+n_perms
                        +" perms (could be because only even permutations are reached)");
            System.out.println("maxdepth="+ maxdepth);
        }
        private int moved_code(int[] subscramble, int mvc) {
            int[] loc=new int[fcnt];
            for (int i=0; i<fcnt; i++)
                loc[i]=i;
            int[] perm=loc.clone();
            int out=0;
            for (int b=fcnt; b>fcnt-wcnt; b--) {
                out*=b;
                int v=loc_id[moved_loc[mvc][subscramble[b-1-(fcnt-wcnt)]]],
                        l=loc[v];
                int ov=perm[b-1];
                out+=l;
                loc[ov]=l;
                perm[l]=ov;
            }
            return out;
        }
        private int[] moved(int[] subscramble, int mvc) {
            int[] out=subscramble.clone();
            for (int i=0; i<subscramble.length; i++)
                out[i]=moved_loc[mvc][subscramble[i]];
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
        public int[] solveAction(int code) { //composition of moves that solve sub-permutation determined with encoded # (code)
            if (depth(code)==-1)
                throw new RuntimeException();
            int[] out=new int[R*C];
            for (int i=0; i<R*C; i++)
                out[i]=i;
            for (int c=code; depth(c)>0; c=par(c))
                out=moved(out,mvc_inv[mvc(c)]);
            return out;
        }
        public int[] scrambleAction(int code) { //==solveAction^(-1)(code)
            int[] tmp=solveAction(code);
            int[] out=new int[R*C];
            for (int i=0; i<R*C; i++)
                out[tmp[i]]=i;
            return out;
        }
        public List<int[]> scrambleMvs(int code) {
            List<int[]> tmp=new ArrayList<>(), out=new ArrayList<>();
            for (int c=code; depth(c)>0; c=par(c))
                tmp.add(mv(c));
            for (int i=tmp.size()-1; i>-1; i--)
                out.add(tmp.get(i));
            return out;
        }
    }
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static int[] inv(int[] mv) {
        return new int[] {mv[0],mv[1],-mv[2]};
    }
    private static List<int[]> inv(List<int[]> mvs) {
        List<int[]> out=new ArrayList<>();
        for (int i=mvs.size()-1; i>-1; i--)
            out.add(inv(mvs.get(i)));
        return out;
    }
    private static int cnt(boolean[] a) {
        int out=0;
        for (boolean b:a) if (b) out++;
        return out;
    }
    private static void addb(boolean[] s, int[] a) {
        for (int i:a)
            s[i]=true;
    }
}
