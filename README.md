# Loopover-Brute-Force-and-Improvement

This program is intended to take a block-building approach to solving Loopover (originally created by carykh) and exploit the symmetries of the puzzle to improve the upper bounds on God's number for Loopover.

NRG version: https://github.com/coolcomputery/Loopover-NRG-Upper-Bounds

## Formal explanation

### BFS Tree

A RxC Loopover is a grid of cells with R rows and C columns, where each row and column can be slided, and each cell has a unique number (see https://loopover.gitlab.io/). The objective is to take a loopover with the numbers scrambled and slide them back into the solved order. Here rows will be indexed from 0 to R-1 top to bottom, and columns will be indexed from 0 to C-1 left to right.

A RxC Loopover in the state "lr x lc" (without the spaces), where lr and lc are binary strings of lengths R and C respectively, is a RxC loopover but with row r locked if lr[r]==0 and column c locked if lr[c]==0. Thus, every piece (r,c) s.t. lr[r]==0 and lc[c]==0 is locked, i.e. it cannot be moved. For example, a 4x4 Loopover in the state "0011x0101" looks like the following, where each locked piece is marked with an "x":

```
x.x.  
x.x.  
....  
....
```

A pair of different Loopover states, "lr0 x lc0"-->"lr1 x lc1", where all locked cells in the first state are also locked in the second state, is called a Loopover phase, as it represents a step during a potential process of solving the entire Loopover board. For example, the phase "11111x11111"-"00111x00111" starts from an unsolved 5x5 board and solves the top-left 2x2 square, and the phase "0011x0101"-->"0001x0100" will take a partially solved 4x4 board and extend the solved region as shown below:
```
x.x.     x.xx  
x.x. --> x.xx  
....     x.xx  
....     ....  
```


Any RxC loopover can be solved by applying one or more phases onto it, progressively solving larger and larger regions of it (this is called block-building), and this gives an upper bound on the "God's number" of RxC Loopover, i.e. the fewest moves necessary to be able to solve every scramble of RxC Loopover.

If a phase is not too big, we can create a BFS tree over it to find optimal solutions to every scramble in that phase. The class ``BFS`` creates these trees for phases consisting of up to ~100-200 million scrambles. The class ``BFSLargeFile`` creates these BFS trees for phases consisting of up to a few tens of billions of scrambles (or however much memory is available on the computer) by writing all the scrambles to a set of external files. It cannot fully store the BFS tree, as it cannot store what the parent scramble of each scramble is, but it does group all scrambles by depth.

### BFS Improvement

The class ``BFS2improve`` takes two BFS trees representing adjacent phases in a Loopover solve, as well as a threshold T. It then iterates over every RxC loopover scramble that would take >T moves to solve if the default solutions provided by the BFS trees were applied. It then tries using an alternative solution for the first phase, such that the total number of moves after applying the second phase become <=T. Alternative solutions for the first phase are tried in increasing order  of move count. Additionally, alternative block-building schemes are applied to solving the scramble in sufficiently few moves. For example, if the BFS trees were "11111x11111"-->"00111x00111" and "00111x00111"-->"00011x00011" over 5x5 Loopover, which represents solving the top-left 2x2 square and then expanding it to a 3x3, the class could try solving a given scramble as "11111x11111"-->"10011x00111"-->"00011x00011" or as "11111x11111"-->"01011x01011"-->"00011x00011" in addition to solving it in the original scheme ("11111x11111"-->"00111x00111"-->"00011x00011").

```
"11111x11111"-->"00111x00111"-->"00011x00011"
.....     xx...     xxx..
.....     xx...     xxx..
..... --> ..... --> xxx..
.....     .....     .....
.....     .....     .....

"11111x11111"-->"10011x00111"-->"00011x00011"
.....     .....     xxx..
.....     xx...     xxx..
..... --> xx... --> xxx..
.....     .....     .....
.....     .....     .....

"11111x11111"-->"01011x01011"-->"00011x00011"
.....     x.x..     xxx..
.....     .....     xxx..
..... --> x.x.. --> xxx..
.....     .....     .....
.....     .....     .....
```

The class also applies a symmetry reduction beforehand to reduce the number of first-phase subscrambles that must be considered. For some schemes, such as "11111x11111"-->"01011x01011"-->"00011x00011", this reduces the number of scrambles by about 8 times.

A very old version of this class, ``LoopoverBruteForce``, was slower and much more restrictive on what kinds of solutions could be found for scrambles that would takes >T moves to solve using the default BFS solutions.

## Known Results

4x4: [GN is 18](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/#post-1444389), found by Tomasz Rokicki using a coset solver.

5x5: GN is between 22 and 44. The lower bound is by [a generating function argument due to xyzzy](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/#post-1333877). The upper bound splits the solving into 4 phases: "11111x11111"-->"01011x01011"-->"00011x00011"-->"00001x00001"-->"00000x00000". Using the class ``BFS2improve``, the first two of these phases have a combined GN of at most 17 and the last two phases have a combined GN of at most 27.

6x6: GN is between 36 and 93. The lower bound is from the scramble consisting of moving all rows 3 units right, followed by moving all columns 3 units down; this can be proven optimal by a Manhattan distance argument. The upper bound splits the solving into the phases "111111x111111"-->"010111x010111"-->"000111x000111"-->"000011x000011"-->"000001x000001"-->"000000x000000". Using the class ``BFS2improve``, the first two phases have a combined GN of at most 24; using ``BFSLargeFile``, the last three phases each have a GN of 21, 24, and 24, respectively.
