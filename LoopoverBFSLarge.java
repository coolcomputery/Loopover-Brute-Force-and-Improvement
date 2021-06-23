import java.io.*;
import java.util.*;
//improved version of LoopoverUpper from https://github.com/coolcomputery/Loopover-Multi-Phase-God-s-Number
//similar to the Tree object in LoopoverBruteForce, but stores permutations in files instead of Java arrays
//for large BFS (up to a few billion permutations)
//to use, first initialize a LoopoverBFSLarge object with the desired parameters
//after that, call the bfs() method to perform the BFS
//      or call the subscramble_code method to convert any number into its scramble
//          (if converting a string, be sure to first convert it into a number using the static num() method)
//          (the conversion depends on the parameters put into the object during construction)
//example of scramble:
//      if id_wloc={0,1,2,4,5,6} and scramble={10,11,3,2,5,6}, this means that
//          piece 0 is at location 10 (row 2 col 2),
//          piece 1 is at location 11 (row 2 col 3),
//          piece 4 is at location 2 (row 0 col 2), etc.
public class LoopoverBFSLarge {
    private int R, C;
    private boolean[] rl, cl, grl, gcl;
    private int[] loc_id, id_floc, id_wloc;
    private int fcnt, wcnt, maxdepth;
    private long nperms;
    private String str;
    private long[] visited; //acts as a set (used in method bfs())
    private int[][] transf, inv_transf;
    public LoopoverBFSLarge(int R, int C, int[] lr, int[] lc, int[] wr, int[] wc) {
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
        nperms=1;
        for (int i=fcnt; i>fcnt-wcnt; i--)
            nperms*=i;
        str=R+"x"+C+"_"
                +Arrays.toString(lr)+"x"+Arrays.toString(lc)+"-"
                +Arrays.toString(wr)+"x"+Arrays.toString(wc);
        System.out.println(str);
        System.out.println("total perms="+nperms);
    }
    public void bfs() throws IOException {
        if (nperms/64+1>Integer.MAX_VALUE)
            throw new RuntimeException("Too many permutations.");
        int nlr=0, nlc=0;
        for (boolean b:rl) if (b) nlr++;
        for (boolean b:cl) if (b) nlc++;
        int[][] moves=new int[2*(R-nlr+C-nlc)][];
        for (int type=0, id=0; type<2; type++) {
            for (int coord=0; coord<(type==0?R:C); coord++)
                if (!(type==0?rl:cl)[coord])
                    for (int shift=-1; shift<=1; shift+=2) {
                        moves[id]=new int[] {type,coord,shift};
                        id++;
                    }
        }
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
    private void add(long n) {
        visited[(int)(n/64)]|=1L<<(n%64);
    }
    private boolean contains(long n) {
        return (visited[(int)(n/64)]&(1L<<(n%64)))!=0;
    }
    private long moved_code(int[] subscramble, int[] mv) {
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
    private long subscramble_code(int[] subscramble) {
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
    private int[] code_subscramble(long code) {
        long pow=1;
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
    private void init_symmetries() {
        boolean flip=R==C;
        int T=flip?8*R*C:4*R*C;
        transf=new int[T][R*C];
        for (int ti=0; ti<T; ti++)
            for (int l=0; l<R*C; l++) {
                int nl=(ti&1)==0?l:(R-1-l/C)*C+l%C; //reflect over horizontal center
                nl=(ti&2)==0?nl:nl/C*C+(C-1-nl%C); //reflect over vertical center
                if (flip) {
                    nl=(ti&4)==0?nl:(nl%C)*C+(nl/C); //flip row and col coords
                    int tri = ti / 8;
                    transf[ti][l] = transloc(R, C, nl, tri / C, tri % C);
                }
                else {
                    int tri = ti / 4;
                    transf[ti][l] = transloc(R, C, nl, tri / C, tri % C);
                }
            }
        inv_transf=new int[T][R*C];
        for (int t=0; t<T; t++) {
            for (int l=0; l<R*C; l++)
                inv_transf[t][transf[t][l]]=l;
        }
    }
    public static void main(String[] args) throws IOException {
        long st=System.currentTimeMillis();
        //bfs(5,5,new int[] {},new int[] {},new int[] {0,1},new int[] {0,1,2});
        //new LoopoverBFSLarge(6,6,new int[] {0,1,2},new int[] {0,1,2},new int[] {3},new int[] {3}).bfs();
        /*System.out.println(
                Arrays.toString(new LoopoverBFSLarge(3,3,new int[] {},new int[] {},new int[] {0,1},new int[] {0,1}).code_subscramble(num("Y=")))
        );//.bfs();*/
        LoopoverBFSLarge l=new LoopoverBFSLarge(4,4,new int[] {},new int[] {},new int[] {0,1,2,3},new int[] {0,1,2,3});
        l.init_symmetries();
        long L=l.nperms/l.transf.length;
        long maxcode=0;
        long checkpt=0;
        double mark=1000000;
        System.out.printf("%20s%15s%15s%15s%n","amt codes processed","cur code #","cur maxcode","ms elapsed");
        //code=163830250637
        for (long code=L, cnt=0; code<l.nperms; code++) {
            int[] subscr=l.code_subscramble(code);
            long min=Long.MAX_VALUE;
            for (int ti=1; ti<l.transf.length; ti++) {
                int[] tsubscr=new int[subscr.length];
                for (int i=0; i<subscr.length; i++)
                    tsubscr[i]=l.inv_transf[ti][subscr[l.transf[ti][i]]];
                min=Math.min(min,l.subscramble_code(tsubscr));
                if (min<maxcode || min<L) break;
            }
            maxcode=Math.max(maxcode,min);
            cnt++;
            if (cnt>=mark) {
                //PREVIOUS: 1778125100   165237421099   163339136465        7175278
                System.out.printf("%20d%15d%15d%15d%n",cnt,code,maxcode,System.currentTimeMillis()-st);
                checkpt++;
                mark=1000000*Math.exp(Math.sqrt(checkpt));
            }
        }
        System.out.println("maxcode="+maxcode);
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static int transloc(int R, int C, int loc, int tr, int tc) {
        return mod(loc/C+tr,R)*C+mod(loc%C+tc,C);
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
