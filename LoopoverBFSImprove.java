import java.util.*;
public class BFS2improve {
    public static String mvseqStr(List<int[]> S) {
        StringBuilder str=new StringBuilder();
        for (int[] m:S)
            str.append(" ").append(m[0]==0?"R":"C").append(m[1]).append(m[2]==1?" ":m[2]==-1?"'":("("+m[2]+")"));
        return str.substring(1);
    }
    private static int[] prod(int[] A, int[] B) { //return [ A[B[i]] for all i ]
        int[] out=new int[B.length];
        for (int i=0; i<B.length; i++) out[i]=A[B[i]];
        return out;
    }
    private static int[] restoringPerm(int[] P, int[] T) {
        //returns permutation Q s.t. prod(P,Q)==T, null if no such Q exists
        Map<Integer,Integer> locs=new HashMap<>();
        for (int i=0; i<P.length; i++)
            locs.put(P[i],i);
        if (locs.size()!=P.length) throw new RuntimeException();
        int[] Q=new int[T.length];
        for (int i=0; i<T.length; i++)
            if (!locs.containsKey(T[i])) return null;
            else Q[i]=locs.get(T[i]);
        return Q;
    }
    private static List<int[]> safeTransformations(int R, int C, List<int[]> ptSets) {
        List<int[]> out=new ArrayList<>();
        System.out.print("\nlist of safe transformations preserving"); for (int[] s:ptSets) System.out.print(" "+Arrays.toString(s)); System.out.println(":");
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
            boolean good=true;
            for (int[] p:ptSets) if (restoringPerm(prod(S,p),p)==null) {
                good=false;
                break;
            }
            if (good) {
                out.add(S);
                System.out.printf("translate (%d,%d); %s%s%s%n",
                        di/C,di%C,
                        r0==1?"flip row coord; ":"",
                        r1==1?"flip clm coord; ":"",
                        r2==1?"transpose":"");
            }
        }
        return out;
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
    /*private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static void checkSolution(int R, int C, int threshold, int[] oscrm, List<List<int[]>> seqs) {
        int mvcnt=0; for (List<int[]> seq:seqs) mvcnt+=seq.size();
        if (mvcnt>threshold) throw new RuntimeException("Too many moves in alternate solution.");
        int N=R*C;
        int[] scrm=oscrm;
        List<int[]> scrms=new ArrayList<>();
        scrms.add(Arrays.copyOf(scrm,N));
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
            scrms.add(Arrays.copyOf(scrm,R*C));
        }
        boolean solved=true;
        for (int i=0; i<N&&solved; i++) if (scrm[i]!=-1&&scrm[i]!=i) solved=false;
        if (!solved) {
            System.out.println("INVALID ALTERNATE SOLUTION");
            System.out.println("seqs=");
            for (List<int[]> tmp:seqs) System.out.println(mvseqStr(tmp));
            for (int i=0; i<scrms.size(); i++) {
                if (i>0) System.out.println("-->");
                printScrm(R,C,scrms.get(i));
            }
            throw new RuntimeException("Invalid alternate solution");
        }
    }*/
    private int R, C, threshold;
    private BFS t0, t1;
    private int[] preblock;
    private int[] scrm(int[] scrm0, int[] scrm1) {
        int[] scrm=new int[R*C]; Arrays.fill(scrm,-1);
        for (int i:preblock) scrm[i]=i;
        for (int i=0; i<t0.T; i++) scrm[t0.target[i]]=scrm0[i];
        for (int i=0; i<t1.T; i++) scrm[t1.target[i]]=scrm1[i];
        return scrm;
    }
    private List<int[]> safeTransforms;
    private int[] distinctScrm0s(int d0) {
        int[] out=new int[t0.fronts.get(d0).length];
        int sz=0;
        boolean[] seen=new boolean[t0.ncombos];
        for (int code0:t0.fronts.get(d0)) if (!seen[code0]) {
            out[sz++]=code0;
            for (int[] S:safeTransforms) {
                int[] scrm0=prod(t0.freeto,t0.decode(code0));
                int[] Q0=restoringPerm(prod(S,t0.target),t0.target);
                scrm0=prod(prod(S,scrm0),Q0);
                int[] fscrm0=prod(t0.tofree,scrm0);
                for (int v:fscrm0) if (v<0) throw new RuntimeException();
                int ncode0=t0.encode(fscrm0);
                if (t0.depth(ncode0)!=d0) throw new RuntimeException();
                seen[ncode0]=true;
            }
        }
        return Arrays.copyOf(out,sz);
    }
    //individual dfs
    private static class DFS {
        private int R, C;
        private BFS pt0, pt1;
        private int[][] t0absmvactions;
        private int[] preblock;
        public DFS(BFS t0, BFS t1) {
            pt0=t0; pt1=t1;
            R=pt0.R; C=pt0.C;
            t0absmvactions=new int[t0.M][];
            for (int m=0; m<t0.M; m++) t0absmvactions[m]=t0.toabsaction(t0.mvactions[m]);
            preblock=new int[R*C]; {
                int K=0;
                for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (!t0.Rf[r]&&!t0.Cf[c]) preblock[K++]=r*C+c;
                preblock=Arrays.copyOf(preblock,K);
            }
            pcode0aftermv=new int[pt0.ncombos][pt0.M];
            for (int code0=0; code0<pt0.ncombos; code0++) {
                for (int mi=0; mi<pt0.M; mi++)
                    pcode0aftermv[code0][mi]=pt0.encode(pt0.decode(code0),pt0.mvactions[mi]);
            }
        }
        private boolean finished;
        private int threshold;
        private int phase0lim;
        private long attempts, nodeVisits;
        private int[][] pcode0aftermv;
        /*private int[] oscrm;
        private List<int[]> p0mvlist;*/
        private void dfs(int code0, int[] part1, int mvs, int prevmi) {
            nodeVisits++;
            if (finished) return;
            if (pt0.depth(code0)==0) {
                attempts++;
                if (mvs+pt1.depth(pt1.encode(part1,pt1.tofree))<=threshold) {
                    finished=true;
                    //checkSolution(R,C,threshold,oscrm,Arrays.asList(p0mvlist,pt1.solvemvs(pt1.encode(part1,pt1.tofree))));
                    return;
                }
            }
            for (int mi:pt0.mvreduc[prevmi]) if (!finished) {
                int ncode0=pcode0aftermv[code0][mi];
                if (mvs+1+pt0.depth(ncode0)<=phase0lim) {
                    //p0mvlist.add(pt0.mvs[mi]);
                    dfs(ncode0,prod(t0absmvactions[mi],part1),mvs+1,mi);
                    //p0mvlist.remove(p0mvlist.size()-1);
                }
            }
        }
        private boolean solveable(int[] scrm, int threshold, int phase0lim) {
            this.threshold=threshold; this.phase0lim=phase0lim;
            finished=false;
            //oscrm=scrm; p0mvlist=new ArrayList<>();
            attempts=0; nodeVisits=0;
            dfs(pt0.encode(prod(scrm,pt0.target),pt0.tofree),prod(scrm,pt1.target),0,pt0.M);
            return finished;
        }
    }
    //aggregate dfs
    /*private int[] oscrm0;
    private List<int[]> t0mvilist;*/
    private int[] t0depth, t1depth;
    private int[][] t0absmvactions, code0aftermv;
    private int phase0lim;
    private int[][] scrm1stosolve;
    private boolean finished;
    private long nodeVisits, attempts;
    private void aggregate_dfs(int code0, int[] netact, int mvs, int prevmi) {
        nodeVisits++;
        if (finished) return;
        if (t0depth[code0]==0) {
            int[][] rem=new int[scrm1stosolve.length][];
            int sz=0;
            for (int[] scrm1:scrm1stosolve) {
                attempts++;
                if (mvs+t1depth[t1.encode(prod(netact,scrm1),t1.tofree)]>threshold) rem[sz++]=scrm1;
                //else checkSolution(R,C,threshold,scrm(oscrm0,scrm1),Arrays.asList(t0mvilist,t1.solvemvs(t1.encode(prod(t1.tofree,prod(netact,scrm1))))));
            }
            scrm1stosolve=Arrays.copyOf(rem,sz);
            if (sz==0) {
                finished=true;
                return;
            }
        }
        for (int mi:t0.mvreduc[prevmi]) if (!finished) {
            int ncode0=code0aftermv[code0][mi];
            if (mvs+1+t0depth[ncode0]<=phase0lim) {
                //t0mvilist.add(t0.mvs[mi]);
                aggregate_dfs(ncode0,prod(t0absmvactions[mi],netact),mvs+1,mi);
                //t0mvilist.remove(t0mvilist.size()-1);å
            }
        }
    }
    private void improve(String S0, String S1, String S2, int thresh, String[] altS1s) {
        t0=new BFS(S0,S1); t1=new BFS(S1,S2);
        R=t0.R; C=t0.C;
        threshold=thresh;
        DFS[] altDFSs=new DFS[altS1s.length];
        for (int a=0; a<altS1s.length; a++)
            altDFSs[a]=new DFS(new BFS(S0,altS1s[a]),new BFS(altS1s[a],S2));
        preblock=new int[R*C]; {
            int K=0;
            for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (!t0.Rf[r]&&!t0.Cf[c]) preblock[K++]=r*C+c;
            preblock=Arrays.copyOf(preblock,K);
        }
        safeTransforms=safeTransformations(R,C,Arrays.asList(preblock,t0.target,t1.target));
        t0absmvactions=new int[t0.M][];
        for (int m=0; m<t0.M; m++) t0absmvactions[m]=t0.toabsaction(t0.mvactions[m]);
        int[][] distinct0s=new int[t0.diam+1][];
        System.out.println("\nreduced phase 0 scrambles depth distribution:");
        for (int d0=0; d0<=t0.diam; d0++) {
            distinct0s[d0]=distinctScrm0s(d0);
            System.out.print((d0>0?" ":"")+d0+":"+distinct0s[d0].length);
        }
        System.out.println();
        long amt=0;
        for (int d0=0; d0<=t0.diam; d0++) for (int d1=0; d1<=t1.diam; d1++) if (d0+d1>threshold)
            amt+=distinct0s[d0].length*(long)t1.fronts.get(d1).length;
        System.out.println("\n# scrambles to improve="+amt);
        t0depth=new int[t0.ncombos];
        code0aftermv=new int[t0.ncombos][t0.M];
        for (int code0=0; code0<t0.ncombos; code0++) {
            t0depth[code0]=t0.depth(code0);
            for (int mi=0; mi<t0.M; mi++)
                code0aftermv[code0][mi]=t0.encode(t0.decode(code0),t0.mvactions[mi]);
        }
        t1depth=new int[t1.ncombos];
        for (int code1=0; code1<t1.ncombos; code1++) t1depth[code1]=t1.depth(code1);
        for (int d0=0; d0<=t0.diam; d0++) for (int d1=0; d1<=t1.diam; d1++) if (d0+d1>threshold) {
            System.out.println("depths "+d0+","+d1+" ("+distinct0s[d0].length*(long)t1.fronts.get(d1).length+" tot scrambles)");
            long cnt=0, cnt0=0, st=System.currentTimeMillis(), mark=st;
            nodeVisits=0; attempts=0;
            String form="%12s%24s%24s%24s%24s%24s%24s%n";
            System.out.printf(form,"time (ms)","scrms","^(-1) * attempts","=","phase 0 scrms","^(-1) * dfs node visits","=");

            int N1=t1.fronts.get(d1).length;
            int[][] t1locs=new int[N1][];
            for (int i=0; i<N1; i++) t1locs[i]=prod(t1.freeto,t1.decode(t1.fronts.get(d1)[i]));
            for (int code0:distinct0s[d0]) {
                int[] t0scrmact=t0.scrmaction(code0);
                scrm1stosolve=new int[N1][];
                for (int i=0; i<N1; i++) scrm1stosolve[i]=prod(t0scrmact,t1locs[i]);
                finished=false;
                //oscrm0=prod(t0.freeto,t0.decode(code0)); t0mvilist=new ArrayList<>();
                int[] scrm0=prod(t0.freeto,t0.decode(code0));
                int[] I=new int[R*C]; for (int i=0; i<R*C; i++) I[i]=i;
                for (phase0lim=d0; !finished&&phase0lim<=threshold; phase0lim++) {
                    aggregate_dfs(code0,I,0,t0.M);
                    int[][] rem=new int[scrm1stosolve.length][];
                    int sz=0;
                    for (int[] scrm1:scrm1stosolve) {
                        boolean solved=false;
                        for (DFS dfs:altDFSs) {
                            solved=dfs.solveable(scrm(scrm0,scrm1),threshold,phase0lim);
                            attempts+=dfs.attempts;
                            nodeVisits+=dfs.nodeVisits;
                            if (solved) break;
                        }
                        if (!solved) rem[sz++]=scrm1;
                    }
                    scrm1stosolve=Arrays.copyOf(rem,sz);
                    if (sz==0) finished=true;
                }
                if (!finished) {
                    System.out.println("NOT REDUCED:");
                    for (int[] scrm1:scrm1stosolve) {
                        printScrm(R,C,scrm(scrm0,scrm1));
                        System.out.println();
                    }
                    return;
                }
                cnt+=t1.fronts.get(d1).length;
                cnt0++;
                long time=System.currentTimeMillis();
                if (time>=mark) {
                    if (mark>st) System.out.printf(form,time-st,cnt,attempts,String.format("%.10f",attempts/(double)cnt),cnt0, nodeVisits,String.format("%.10f", nodeVisits /(double)cnt0));
                    mark+=100_000;
                }
            }
            if (mark>st) System.out.printf(form,System.currentTimeMillis()-st,cnt,attempts,String.format("%.10f",attempts/(double)cnt),cnt0, nodeVisits,String.format("%.10f", nodeVisits /(double)cnt0));
        }
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        new BFS2improve().improve("000011x000011","000001x000011","000001x000001",25,new String[] {"000011x000001"});
        System.out.println("total program time="+(System.currentTimeMillis()-st));
    }
}
