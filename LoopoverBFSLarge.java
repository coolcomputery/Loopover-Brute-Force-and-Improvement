import java.io.*;
import java.util.*;
//improved version of LoopoverUpper from https://github.com/coolcomputery/Loopover-Multi-Phase-God-s-Number
//similar to LoopoverBFS, but stores permutations in files instead of Java arrays
//for large BFS (up to a few billion permutations)
//to use, first initialize a LoopoverBFSLarge object with the desired parameters
//after that, call the bfs() method to perform the BFS
public class LoopoverBFSLarge {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static boolean[] mask(String s) {
        boolean[] out=new boolean[s.length()];
        for (int i=0; i<s.length(); i++)
            out[i]=s.charAt(i)=='1';
        return out;
    }
    //define absolute indexing as mapping coordinate (r,c) to index r*C+c
    //every scramble is represented by an array L[], where piece i is at location L[i]
    private String folder;
    private int R, C;
    private int Nfree;
    private boolean[] Rfree, Cfree;
    //a location (r,c) is free iff Rfree[r]||Cfree[c]
    private int[] tofree, freeto;
    //tofree[r*C+c]=i, where free location (r,c) is assigned to index i
    public int K;
    private int[] solvedscrm;
    private long solvedscrmcode;
    private int[][] mvactions, mvs, mvreduc;
    private int M;
    public long ncombos;
    //bfs stuff
    private long[] visited;
    public int D;
    private int codelen, mvilen;
    private void add(long n) {
        visited[(int)(n/64)]|=1L<<(n%64);
    }
    private boolean contains(long n) {
        return (visited[(int)(n/64)]&(1L<<(n%64)))!=0;
    }
    public LoopoverBFSLarge(int R, int C, String rf0, String cf0, String rf1, String cf1) {
        folder=R+"x"+C+"-"+rf0+"x"+cf0+"-"+rf1+"x"+cf1+"\\";
        System.out.println(folder);
        new File(folder).mkdir();
        this.R=R; this.C=C;
        Rfree=mask(rf0); Cfree=mask(cf0);
        tofree=new int[R*C]; freeto=new int[R*C];
        Nfree=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if (Rfree[r]||Cfree[c]) {
                    tofree[r*C+c]=Nfree;
                    freeto[Nfree]=r*C+c;
                    Nfree++;
                }
                else tofree[r*C+c]=-1;
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%3d",tofree[r*C+c]);
            System.out.println();
        }
        boolean[] Rnfree=mask(rf1), Cnfree=mask(cf1);
        K=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    K++;
        solvedscrm=new int[K];
        for (int r=0, idx=0; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    solvedscrm[idx++]=tofree[r*C+c];
        System.out.println(Arrays.toString(solvedscrm));
        ncombos=1;
        for (int rep=0; rep<K; rep++) ncombos*=Nfree-rep;
        System.out.println("ncombos="+ncombos);
        if (ncombos/64>400_000_000) throw new RuntimeException("Too many combinations to handle.");
        codelen=bb95(ncombos).length();
        mvilen=bb95(M).length();
        System.out.println("every combo represented with "+ codelen +" characters");
        //moves: every move is represented with [t,a,r]:
        //t: type (0=row shift, 1=clm shift)
        //a: the a-th (row if t==0, else clm)
        //r: # units to shift (right if t==0, else down)
        M=0;
        for (boolean b:Rfree) if (b) M+=2;
        for (boolean b:Cfree) if (b) M+=2;
        mvactions=new int[M][]; mvs=new int[M][]; {
            //mvactions[m][i]=free loc. that i-th free loc. will go to after move m is applied
            int idx=0;
            for (int mr=0; mr<R; mr++)
            if (Rfree[mr])
            for (int s=-1; s<=1; s+=2) {
                mvs[idx]=new int[] {0,mr,s};
                mvactions[idx]=new int[Nfree];
                for (int r=0; r<R; r++)
                    for (int c=0; c<C; c++)
                        if (Rfree[r]||Cfree[c])
                            mvactions[idx][tofree[r*C+c]]=tofree[r*C+(r==mr?mod(c+s,C):c)];
                idx++;
            }
            for (int mc=0; mc<C; mc++)
            if (Cfree[mc])
            for (int s=-1; s<=1; s+=2) {
                mvs[idx]=new int[] {1,mc,s};
                mvactions[idx]=new int[Nfree];
                for (int r=0; r<R; r++)
                    for (int c=0; c<C; c++)
                        if (Rfree[r]||Cfree[c])
                            mvactions[idx][tofree[r*C+c]]=tofree[(c==mc?mod(r+s,R):r)*C+c];
                idx++;
            }
        }
        mvreduc=new int[M+1][];
        for (int m=0; m<M; m++) {
            List<Integer> l=new ArrayList<>();
            for (int m2=0; m2<M; m2++)
                if (mvs[m][0]!=mvs[m2][0]
                        ||mvs[m][1]<mvs[m2][1]
                        ||(mvs[m][1]==mvs[m2][1]&&mvs[m][2]+mvs[m2][2]!=0))
                    l.add(m2);
            mvreduc[m]=new int[l.size()];
            for (int i=0; i<l.size(); i++)
                mvreduc[m][i]=l.get(i);
        }
        mvreduc[M]=new int[M];
        for (int i=0; i<M; i++) mvreduc[M][i]=i;
        //move sequence reduction
        //when doing two moves of the same type, one after the other: [t,a,r], [t,b,s]:
        //WLOG a<=b, or else the two moves can be arranged to satisfy this condition without changing the final scramble
        //if a==b, then r+s!=0, else the two moves cancel each other out
        /*mvreduc=new int[M+1][];
        for (int m=0; m<M; m++) {
            List<Integer> l=new ArrayList<>();
            for (int m2=0; m2<M; m2++)
                if (mvs[m][0]!=mvs[m2][0]
                        ||mvs[m][1]<mvs[m2][1]
                        ||(mvs[m][1]==mvs[m2][1]&&mvs[m][2]+mvs[m2][2]!=0))
                    l.add(m2);
            mvreduc[m]=new int[l.size()];
            for (int i=0; i<l.size(); i++)
                mvreduc[m][i]=l.get(i);
        }
        mvreduc[M]=new int[M];
        for (int i=0; i<M; i++) mvreduc[M][i]=i;*/
    }
    public void bfs() throws IOException {
        //BFS
        visited=new long[(int)(ncombos/64+1)];
        solvedscrmcode=comboCode(solvedscrm);
        add(solvedscrmcode);
        PrintWriter fout=new PrintWriter(new FileWriter(folder+"0.txt"));
        fout.print(bb95j(solvedscrmcode,codelen).append(bb95j(0,mvilen)));
        fout.close();
        System.out.println("0:1");
        long reached=1;
        D=0;
        while (true) {
            BufferedReader fin=new BufferedReader(new FileReader(folder+D+".txt"));
            fout=new PrintWriter(new FileWriter(folder+(D+1)+".txt"));
            StringBuilder toPrint=new StringBuilder();
            long sz=0;
            while (true) {
                StringBuilder code=new StringBuilder();
                for (int i=0; i<codelen; i++) {
                    int r=fin.read();
                    if (r==-1) break;
                    code.append((char)r);
                }
                if (code.length()==0) break;
                if (code.length()!=codelen) throw new RuntimeException("\""+code+"\".length()!="+codelen);
                long f=num(code.toString());
                int[] scrm=codeCombo(f);
                StringBuilder mvibb95=new StringBuilder();
                for (int i=0; i<mvilen; i++)
                    mvibb95.append((char)fin.read());
                int mvi=(int)num(mvibb95.toString());
                int[] mvlist=mvreduc[f==solvedscrmcode?M:mvi];
                for (int mi:mvlist) {
                    long nf=comboCode(scrm,mvactions[mi]);
                    if (!contains(nf)) {
                        add(nf);
                        toPrint.append(bb95j(nf,codelen)).append(bb95j(mi,mvilen));
                        sz++;
                        if (sz%1000_000==0) {
                            fout.print(toPrint);
                            toPrint=new StringBuilder();
                        }
                    }
                }
            }
            fout.print(toPrint);
            fout.close();
            if (sz==0) break;
            D++;
            System.out.println(D+":"+sz);
            reached+=sz;
        }
        System.out.println("#reached="+reached);
        System.out.println("D="+D);
    }
    /*
    encoding ordered combinations
    A[0]...A[K-1], 0<=A[i]<N, all A[i] distinct
    possible to transform permutation [0...N-1] into [....|A]
    using a sequence of swaps (i,J_i) for i=N-1 to N-K inclusive
      --> encode A as J_(N-1)+N*(J_(N-2)+(N-1)*(...+(N-K+2)*J_(N-K)...)
    for this program, N=Nfree, K=K
    */
    private long comboCode(int[] A) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i=Nfree-1; i>=Nfree-K; i--) {
            //swap idxs i and L[A[i-(N-K)]] in P
            int j=L[A[i-(Nfree-K)]];
            int pi=P[i];//, pj=P[j];
            //P[i]=pj; //<--idx i will never be touched again
            P[j]=pi;
            L[pi]=j;
            //L[pj]=i;
            //J_i==j
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    private long comboCode(int[] A, int[] f) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i=Nfree-1; i>=Nfree-K; i--) {
            int j=L[f[A[i-(Nfree-K)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    private int[] codeCombo(long code) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        for (int v=Nfree; v>Nfree-K; v--) {
            int i=v-1, j=(int)(code%v);
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[K];
        System.arraycopy(P,Nfree-K,out,0,K);
        return out;
    }
    public static void main(String[] args) throws IOException {
        long st=System.currentTimeMillis();
        new LoopoverBFSLarge(5,5
                ,"11111","11111"
                ,"00111","00011"
        ).bfs();
        //new LoopoverBFSLarge(4,4,"0011","0001","0000","0000").bfs();
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
    private static StringBuilder bb95j(long n, int len) { //BACKWARDS base 95
        StringBuilder tmp=new StringBuilder();
        while (n>0) {
            tmp.append((char)(n%95+32));
            n/=95;
        }
        while (tmp.length()<len) tmp.append(' ');
        return tmp;
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
        for (int i=bb95.length()-1; i>-1; i--)
            out=out*95+(bb95.charAt(i)-32);
        return out;
    }
}
