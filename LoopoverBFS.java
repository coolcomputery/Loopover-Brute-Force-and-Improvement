import java.io.*;
import java.util.*;
//improved version of LoopoverUpper from https://github.com/coolcomputery/Loopover-Multi-Phase-God-s-Number
//similar to the Tree object in LoopoverBruteForce, but stores permutations in files instead of Java arrays
//for large BFS (up to a few billion permutations)
public class LoopoverBFS {
    private static int R, C;
    private static boolean[] rl, cl, grl, gcl;
    private static int[] loc_id, id_floc, id_wloc;
    private static int fcnt, wcnt, maxdepth;
    private static long nperms;
    private static String str;
    private static long[] visited; //acts as a set
    public static void bfs(int R, int C, int[] lr, int[] lc, int[] wr, int[] wc) throws IOException {
        LoopoverBFS.R=R;
        LoopoverBFS.C=C;
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
        int[][] moves=new int[2*(R-nlr+C-nlc)][];
        for (int type=0, id=0; type<2; type++) {
            for (int coord=0; coord<(type==0?R:C); coord++)
                if (!(type==0?rl:cl)[coord])
                    for (int shift=-1; shift<=1; shift+=2) {
                        moves[id]=new int[] {type,coord,shift};
                        id++;
                    }
        }
        nperms=1;
        for (int i=fcnt; i>fcnt-wcnt; i--)
            nperms*=i;
        str=R+"x"+C+"_"
                +Arrays.toString(lr)+"x"+Arrays.toString(lc)+"-"
                +Arrays.toString(wr)+"x"+Arrays.toString(wc);
        System.out.println(str);
        System.out.println("total perms="+nperms);
        if (nperms/64+1>Integer.MAX_VALUE)
            throw new RuntimeException("Too many permutations.");
        visited=new long[(int)(nperms/64+1)];
        maxdepth =0;
        long initcode=subscramble_code(id_wloc);
        System.out.println(Arrays.toString(id_wloc));
        add(initcode);
        PrintWriter out=new PrintWriter(new FileWriter(str+"\\0.txt"));
        out.println(bb95(initcode));
        out.close();
        long reached=1;
        while (true) {
            BufferedReader in=new BufferedReader(new FileReader(str+"\\"+maxdepth+".txt"));
            out=new PrintWriter(new FileWriter(str+"\\"+(maxdepth+1)+".txt"));
            int sz=0;
            StringBuilder toprint=new StringBuilder();
            while (true) {
                String l=in.readLine();
                if (l==null)
                    break;
                int[] subscramble=code_subscramble(num(l));
                for (int[] mv:moves) {
                    long nc=moved_code(subscramble,mv);
                    if (!contains(nc)) {
                        add(nc);
                        toprint.append(bb95(nc)).append("\n");
                        sz++;
                        reached++;
                        if (sz%1000_000==0) { //StringBuilder speeds things up a bit
                            out.print(toprint);
                            toprint=new StringBuilder();
                        }
                    }
                }
            }
            out.print(toprint);
            out.close();
            if (sz==0)
                break;
            maxdepth++;
            System.out.println(maxdepth +":"+sz);
        }
        if (reached<nperms)
            System.out.println("!!!ONLY REACHED "+reached+"/"+nperms
                    +" (could be because only even permutations are reached)");
        System.out.println("maxdepth="+ maxdepth);
    }
    private static void add(long n) {
        visited[(int)(n/64)]|=1L<<(n%64);
    }
    private static boolean contains(long n) {
        return (visited[(int)(n/64)]&(1L<<(n%64)))!=0;
    }
    private static long moved_code(int[] subscramble, int[] mv) {
        int[] loc=new int[fcnt];
        for (int i=0; i<fcnt; i++)
            loc[i]=i;
        int[] perm=loc.clone();
        long out=0;
        for (int b=fcnt; b>fcnt-wcnt; b--) {
            out*=b;
            int i=subscramble[b-1-(fcnt-wcnt)],
                    r=i/C, c=i%C;
            int v=loc_id[
                    mv[0]==0 && r==mv[1]?
                            (r*C+mod(c+mv[2],C)):
                            mv[0]==1 && c==mv[1]?
                                    (mod(r+mv[2],R)*C+c):
                                    i],
                    l=loc[v];
            int ov=perm[b-1];
            out+=l;
            loc[ov]=l;
            perm[l]=ov;
        }
        return out;
    }
    private static long subscramble_code(int[] subscramble) {
        int[] loc=new int[fcnt];
        for (int i=0; i<fcnt; i++)
            loc[i]=i;
        int[] perm=loc.clone();
        long out=0;
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
    private static int[] code_subscramble(long code) {
        int pow=1;
        for (int i=fcnt-wcnt+1; i<fcnt; i++)
            pow*=i;
        int[] perm=new int[fcnt];
        for (int i=0; i<fcnt; i++)
            perm[i]=i;
        for (int id=fcnt-1; id>fcnt-1-wcnt; id--) {
            int idx=(int)(code/pow);
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
    public static void main(String[] args) throws IOException {
        long st=System.currentTimeMillis();
        //bfs(5,5,new int[] {},new int[] {},new int[] {0,1},new int[] {0,1,2});
        bfs(6,6,new int[] {0,1,2},new int[] {0,1,2},new int[] {3},new int[] {3});
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static StringBuilder bb95(long n) { //BACKWARDS base 95
        if (n==0) return new StringBuilder(" ");
        StringBuilder tmp=new StringBuilder();
        while (n>0) {
            tmp.append((char)(n%95+32));
            n/=95;
        }
        return tmp;
    }
    private static long num(String bb95) {
        long out=0;
        for (int i=bb95.length()-1; i>-1; i--/*int i=0; i<bb95.length(); i++*/) {
            out*=95;
            out+=bb95.charAt(i)-32;
        }
        return out;
    }
}
