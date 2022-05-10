import java.util.*;
/**
 * Upper bounds God's number of expanding solved region S0 to S2, via solving S1
 *  by making BFS trees for S0-->S1 and S1-->S2,
 *  taking all scrambles that would take >T moves to solve
 *      using the default solution move sequences from applying the trees,
 *  and finding alternative solutions to them consisting of <=T moves
 */
public class BFS2improve {
    public static String mvseqsStr(List<List<int[]>> Ss) {
        StringBuilder str=new StringBuilder();
        for (List<int[]> S:Ss) {
            for (int[] mvn:S) str.append(" ").append(BFS.mvnameStr(mvn));
            str.append("\n");
        }
        return str.substring(1);
    }
    private static void printScrm(int R, int C, int[] scrm) {
        int[] board=new int[R*C]; Arrays.fill(board,-1);
        for (int i=0; i<R*C; i++) if (scrm[i]!=-1) board[scrm[i]]=i;
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++) {
                int v=board[r*C+c];
                if (R*C<=26) System.out.print(v==-1?".":(char)(v+'A'));
                else System.out.printf("%3s",v==-1?".":v);
            }
            System.out.println();
        }
    }
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static int[] concat(int[]... As) {
        int s=0; for (int[] A:As) s+=A.length;
        int[] out=new int[s];
        int i=0;
        for (int[] A:As) {
            System.arraycopy(A,0,out,i,A.length);
            i+=A.length;
        }
        return out;
    }
    private static int[] prod(int[] A, int[] B) { //return [ A[B[i]] for all i ]
        int[] out=new int[B.length];
        for (int i=0; i<B.length; i++) out[i]=A[B[i]];
        return out;
    }
    private static int[] restoringPerm(int[] S, int[] T) {
        //returns permutation Q s.t. prod(prod(S,T),Q)==T, or null if no such Q exists
        Map<Integer,Integer> locs=new HashMap<>();
        int[] P=prod(S,T);
        for (int i=0; i<P.length; i++)
            locs.put(P[i],i);
        if (locs.size()!=P.length) throw new RuntimeException();
        int[] Q=new int[T.length];
        for (int i=0; i<T.length; i++)
            if (!locs.containsKey(T[i])) return null;
            else Q[i]=locs.get(T[i]);
        if (!Arrays.equals(prod(P,Q),T)) throw new RuntimeException();
        return Q;
    }
    public static int[] partialBoard(int R, int C, int[] pieces, int[] locations) {
        int[] scrm=new int[R*C]; Arrays.fill(scrm,-1);
        for (int i=0; i<pieces.length; i++) scrm[pieces[i]]=locations[i];
        return scrm;
    }
    public static void checkSolution(int R, int C, int threshold, int[] oscrm, List<List<int[]>> seqs) {
        int mvcnt=0; for (List<int[]> seq:seqs) mvcnt+=seq.size();
        if (mvcnt>threshold) {
            System.out.println("TOO MANY MOVES USED (>"+threshold+")\n"+mvseqsStr(seqs));
            printScrm(R,C,oscrm);
            throw new RuntimeException("Solution contains >"+threshold+" moves.");
        }
        int N=R*C;
        int[] scrm=oscrm;
        List<int[]> scrms=new ArrayList<>(Collections.singletonList(Arrays.copyOf(scrm,N)));
        for (List<int[]> seq:seqs) {
            for (int[] mv:seq) {
                int mcoord=mv[1], s=mv[2];
                int[] nscrm=new int[N];
                for (int i=0; i<N; i++)
                    if (scrm[i]==-1) nscrm[i]=-1;
                    else {
                        int r=scrm[i]/C, c=scrm[i]%C;
                        nscrm[i]=mv[0]==0?(r*C+(r==mcoord?mod(c+s,C):c)):
                                ((c==mcoord?mod(r+s,R):r)*C+c);
                    }
                scrm=nscrm;
            }
            scrms.add(Arrays.copyOf(scrm,N));
        }
        for (int i=0; i<N; i++) if (scrm[i]!=-1&&scrm[i]!=i) {
            System.out.println("INVALID SOLUTION"+"\nseqs="+mvseqsStr(seqs));
            for (int si=0; si<scrms.size(); si++) {
                if (si>0) System.out.println("-->");
                printScrm(R,C,scrms.get(si));
            }
            throw new RuntimeException("Incorrect solution.");
        }
    }
    private static List<int[][]> rigidSymmetries(int R, int C) {
        List<int[][]> out=new ArrayList<>();
        for (int transp=0; transp<(R==C?2:1); transp++) for (int flipr=0; flipr<2; flipr++) for (int flipc=0; flipc<2; flipc++)
            for (int tr=0; tr<R; tr++) for (int tc=0; tc<C; tc++) {
                int[] S=new int[R*C];
                for (int r=0; r<R; r++) for (int c=0; c<C; c++) {
                    int nr=r, nc=c;
                    if (transp==1) { int t=nr; nr=nc; nc=t; }
                    if (flipr==1) nr=R-1-nr;
                    if (flipc==1) nc=C-1-nc;
                    nr=(nr+tr)%R; nc=(nc+tc)%C;
                    S[r*C+c]=nr*C+nc;
                }
                out.add(new int[][] {{transp,flipr,flipc,tr,tc},S});
            }
        return out;
    }
    private static void improve(String state0, String state1, String state2, int threshold, boolean check, int LIM) {
        System.out.printf("state0=%s state1=%s state2=%s\nthreshold=%d\ncheck=%s%n",state0,state1,state2,threshold,check);
        BFS_DFS ptree=LIM<0?null:new BFS_DFS(state0,state2,LIM);
        long pbfs_size=ptree==null?Long.MAX_VALUE:ptree.nfound();
        BFS treea=new BFS(state0,state1), treeb=new BFS(state1,state2);
        int R=treea.R, C=treea.C;
        System.out.println("allowed symmetries:");
        List<int[][]> symmTransforms=new ArrayList<>(); {
            int[] S2=concat(treeb.preblock,treeb.target), target=concat(treea.target,treeb.target);
            for (int[][] symm:rigidSymmetries(R,C)) {
                int[] S=symm[1];
                if (restoringPerm(S,treea.preblock)!=null && restoringPerm(S,S2)!=null) {
                    int[] Q=restoringPerm(S,target);
                    symmTransforms.add(new int[][] {S,Q});

                    int[] name=symm[0];
                    String s=(name[0]==1?"transpose ":"")+(name[1]==1?"flip row ":"")+(name[2]==1?"flip clm ":"")
                            +(name[3]!=0 || name[4]!=0?"translate <"+name[3]+","+name[4]+">":"");
                    if (s.equals("")) s="identity";
                    if (s.charAt(s.length()-1)==' ') s=s.substring(0,s.length()-1);
                    System.out.println(s+" "+Arrays.toString(Q));
                }
            }
        }

        long tot=0;
        for (int da=0; da<=treea.diam; da++) for (int db=0; db<=treeb.diam; db++) if (da+db>threshold)
            tot+=treea.fronts.get(da).length*(long)treeb.fronts.get(db).length;
        System.out.println("tot # scrambles to consider="+tot);
        System.out.println("symmetry reduction --> ~"+tot/(double)symmTransforms.size()+" scrambles");
        long tot_st=System.currentTimeMillis(), tot_symmReduc_t=0;
        for (int da=0; da<=treea.diam; da++) if (da+treeb.diam>threshold) {
            int[] reducedScrmas=new int[treea.fronts.get(da).length];
            List<List<int[][]>> transformsToCheck=new ArrayList<>(); {
                int n=0;
                for (int ca:treea.fronts.get(da)) {
                    int[] ra=prod(treea.f2a,treea.decode(ca));
                    int[] pscrm=new int[treea.T+treeb.T];
                    //^^^^^ partial scramble (list of locations that tiles treea.target||treeb.target are at
                    Arrays.fill(pscrm,-1);
                    System.arraycopy(ra,0,pscrm,0,treea.T);
                    boolean good=true;
                    List<int[][]> transformsList=new ArrayList<>();
                    for (int[][] symm:symmTransforms) {
                        int[] S=symm[0], Q=symm[1];
                        int[] npscrm=prod(pscrm,Q);
                        //determine as many elements of prod(S,prod(pscrm,Q)) as possible
                        for (int i=0; i<npscrm.length; i++)
                            npscrm[i]=npscrm[i]==-1?-1:S[npscrm[i]];
                        int comp=0, i=0;
                        for (; i<treea.T && npscrm[i]!=-1; i++) {
                            int v=pscrm[i], nv=npscrm[i];
                            if (v>nv) {
                                comp=1;
                                break;
                            }
                            else if (v<nv) {
                                comp=-1;
                                break;
                            }
                        }
                        //comp=-1: definitely smaller (lexicographically); 1: definitely larger; 0: cannot be determined
                        if (comp>0) {
                            good=false;
                            break;
                        }
                        if (comp==0) transformsList.add(new int[][] {S,Q,{i}});
                    }
                    if (good) {
                        reducedScrmas[n++]=ca;
                        transformsToCheck.add(transformsList);
                    }
                }
                reducedScrmas=Arrays.copyOf(reducedScrmas,n);
            }
            System.out.printf("da=%d #scrmas=%d%n",da,reducedScrmas.length);

            for (int db=0; db<=treeb.diam; db++) if (da+db>threshold) {
                System.out.printf("da=%d db=%d #scrms <=%d --> ~%f%n",da,db,
                        reducedScrmas.length*(long)treeb.fronts.get(db).length,
                        (treea.fronts.get(da).length*(long)treeb.fronts.get(db).length)/(double)symmTransforms.size());

                List<int[]> rbs=new ArrayList<>();
                for (int cb:treeb.fronts.get(db))
                    rbs.add(prod(treeb.f2a,treeb.decode(cb)));

                class HELP {
                    int[] scrambledBoard(int[] pcsa, int[] pcsb) {
                        return partialBoard(R,C,concat(treea.preblock,treea.target,treeb.target),concat(treea.preblock,pcsa,pcsb));
                    }

                    String arr2jstr(long[] A) {
                        StringBuilder s=new StringBuilder();
                        for (long v:A) s.append(String.format(" %15d",v));
                        return s.toString();
                    }
                    final String stats="t=%16d symmReduc_time,scrms,transforms,work=%16d,%16d,%16d,%16d  scrmas=%12d  scrms=%16d  dfsWork=%20d solas=%16d  attempts=%20d attempts/scrm=%12.4f hist_la=%s hist_l=%s%n"
                            +(ptree==null?"":String.format("%-143s","tough scrambles:")+" $scrms=%16d $dfsWork=%20d"+String.format("%24s","")+"$attempts=%20d"+String.format("%28s","")+"$hist_l=%s%n");
                    long st=System.currentTimeMillis(), mark=0, symmReduc_time=0, symmReduc_scrms=0, symmReduc_transforms=0, symmReduc_work=0;
                    long scrmas=0, scrms=0,
                            dfsWork=0, solas=0, attempts=0; long[] hist_la=new long[threshold+1], hist_l=new long[threshold+1];
                    long $scrms=0,
                            $dfsWork=0, $attempts=0; long[] $hist_l=new long[threshold+1];
                    public void printStats() {
                        if (ptree==null) System.out.printf(stats,System.currentTimeMillis()-st,symmReduc_time,symmReduc_scrms,symmReduc_transforms,symmReduc_work,scrmas,scrms,dfsWork,solas,attempts,attempts/(double)scrms,
                                arr2jstr(hist_la),arr2jstr(hist_l));
                        else System.out.printf(stats,System.currentTimeMillis()-st,symmReduc_time,symmReduc_scrms,symmReduc_transforms,symmReduc_work,scrmas,scrms,dfsWork,solas,attempts,attempts/(double)scrms,
                                arr2jstr(hist_la),arr2jstr(hist_l),
                                $scrms,$dfsWork,$attempts,arr2jstr($hist_l));
                    }
                    public void log() {
                        long time=System.currentTimeMillis()-st;
                        if (time>=mark) {
                            if (mark>0) printStats();
                            mark+=mark<60_000?10_000:mark<600_000?60_000:mark<3600_000?600_000:3600_000;
                        }
                    }
                } HELP HELP=new HELP();

                for (int ai=0; ai<reducedScrmas.length; ai++) {
                    int ca=reducedScrmas[ai];
                    int[] ra=prod(treea.f2a,treea.decode(ca));
                    int[] scrma=treea.scrmaction(ca), fscrma=prod(treea.a2f,prod(scrma,treea.f2a));
                    //scrma=scramble action over the entire board, using the default move sequence found by treea,
                    //  that transforms pieces treea.target to treea.decode(ca);
                    //fscrma is defined s.t. if scrma[a]=b and both a and b are free locations in treea, then fscrma[treea.a2f[a]]=treea.a2f[b]

                    List<int[][]> transformsList=transformsToCheck.get(ai);
                    List<int[]> tosolve=new ArrayList<>(); {
                        HELP.symmReduc_time-=System.currentTimeMillis();
                        int[] locs=Arrays.copyOf(ra,treea.T+treeb.T);
                        for (int[] rb:rbs) {
                            HELP.symmReduc_scrms++;
                            //locs=ra || scrma*rb
                            for (int bi=0; bi<treeb.T; bi++) locs[treea.T+bi]=scrma[rb[bi]];
                            boolean canonical=true; //symmetry reduction
                            for (int[][] symm:transformsList) {
                                HELP.symmReduc_transforms++;
                                int[] S=symm[0], Q=symm[1];
                                //lexicographically compare locs with symm[0]*locs*symm[1], where A*B represents prod(A,B)
                                boolean good=true;
                                for (int i=symm[2][0]; i<locs.length; i++) {
                                    HELP.symmReduc_work++;
                                    int v=locs[i], nv=S[locs[Q[i]]];
                                    if (v>nv) {
                                        good=false;
                                        break;
                                    }
                                    else if (v<nv) break;
                                }
                                if (!good) {
                                    canonical=false;
                                    break;
                                }
                            }
                            if (canonical) tosolve.add(rb);
                        }
                        HELP.symmReduc_time+=System.currentTimeMillis();
                    }

                    class DFS {
                        int[] ftargeta=prod(treea.a2f,treea.target);
                        long nattempts;
                        int maxla;
                        int[][] mvseq;
                        void dfs(int la, int[] faction, int pmi) {
                            if (ptree!=null && nattempts>=pbfs_size*tosolve.size()) return;
                            if ((HELP.dfsWork&127)==0) HELP.log();
                            if (tosolve.size()==0) return;
                            HELP.dfsWork++;
                            //only accept move sequence as solution if it is exactly maxla moves long and solves phase a without having solved it earlier in the sequence
                            int[] fra=prod(faction,ftargeta);
                            int deptha=treea.depth[treea.encode(fra)];
                            if (la==maxla && deptha==0) {
                                HELP.solas++;
                                int[] action_bf=prod(treeb.a2f,treea.toabsaction(faction));
                                List<int[]> rem=new ArrayList<>();
                                for (int[] rb:tosolve) {
                                    HELP.attempts++; nattempts++;
                                    int ncb=treeb.encodeprod(action_bf,rb), l=la+treeb.depth[ncb];
                                    if (l<=threshold) {
                                        HELP.scrms++; HELP.hist_la[la]++; HELP.hist_l[l]++;
                                        if (check) checkSolution(R,C,threshold,
                                                HELP.scrambledBoard(ra,prod(scrma,rb)),
                                                Arrays.asList(Arrays.stream(mvseq).toList(),treeb.solvemvs(ncb)));
                                    }
                                    else rem.add(rb);
                                }
                                tosolve.clear();
                                tosolve.addAll(rem);
                                return;
                            }
                            if (la==maxla || deptha==0) return;
                            for (int mi:treea.mvreduc[pmi])
                                if (la+1+treea.depth[treea.encodeprod(treea.mvfactions[mi],fra)]<=maxla) {
                                    if (check) mvseq[la]=treea.mvnames[mi];
                                    dfs(la+1,prod(treea.mvfactions[mi],faction),mi);
                                }
                        }
                        void solve(int la) {
                            this.maxla=la;
                            if (check) mvseq=new int[la][];
                            dfs(0,fscrma,treea.M);
                        }
                    }
                    int maxla=da;
                    DFS dfs=new DFS(); dfs.nattempts=0;
                    for (; maxla<=threshold && tosolve.size()>0; maxla++)
                        dfs.solve(maxla);
                    for (int[] rb:tosolve) {
                        HELP.log();
                        int[] pboard=HELP.scrambledBoard(ra,prod(scrma,rb));
                        List<int[]> sol=ptree==null?null:ptree.sol(prod(pboard,ptree.target),threshold-LIM);
                        if (sol==null) {
                            System.out.println("NOT SOLVEABLE IN <="+threshold+" MOVES");
                            printScrm(R,C,HELP.scrambledBoard(ra,prod(scrma,rb)));
                            return;
                        }
                        else {
                            HELP.$scrms++; HELP.$dfsWork+=ptree.nnodes; HELP.$attempts+=ptree.nattempts; HELP.$hist_l[sol.size()]++;
                            if (check) checkSolution(R,C,threshold,pboard,Collections.singletonList(sol));
                        }
                    }
                    HELP.scrmas++;
                }
                HELP.printStats();
                tot_symmReduc_t+=HELP.symmReduc_time;
            }
        }
        System.out.printf("total improvement time=%d%n",System.currentTimeMillis()-tot_st);
        System.out.println("total time spent on symmetry reduction="+tot_symmReduc_t);
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        improve(args[0],args[1],args[2],Integer.parseInt(args[3]),args.length>4 && Boolean.parseBoolean(args[4]),args.length>5?Integer.parseInt(args[5]):-1);
        System.out.println("total program time="+(System.currentTimeMillis()-st));
    }
}
