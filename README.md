# Loopover-Brute-Force-and-Improvement

This program is intended to take a block-building approach to solving Loopover (originally created by carykh) and exploit the symmetries of the puzzle to improve the upper bounds on God's number for Loopover.

NRG version: https://github.com/coolcomputery/Loopover-NRG-Upper-Bounds

## Formal explanation

### Loopover

A RxC Loopover is a grid of cells with R rows and C columns, where each row and column can be slided, and each cell has a unique number (see https://loopover.xyz/). The objective is to take a loopover with the numbers scrambled and slide them back into the solved order. Here rows will be indexed from 0 to R-1 top to bottom, and columns will be indexed from 0 to C-1 left to right.

A single move consists of moving a row one unit left/right, or moving a column one unit down/up.

### BFS Tree

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

If a phase is not too big, we can create a BFS tree over it to find optimal solutions to every scramble in that phase. The class ``BFS`` creates these trees for phases consisting of up to ~100-200 million scrambles. The class ``BFSLowMemory`` (old version ``BFSLargeFile``) creates these BFS trees for phases consisting of up to a few tens of billions of scrambles (or however much memory is available on the computer) by storing a bitset of what nodes have been seen, and another bitset of what nodes are at the current BFS depth, in two large files. It does not store the BFS tree in memory, but it does print our the code numbers of all antipodes (nodes at the deepest level of the tree).

### BFS Improvement

The class ``BFS2improve`` takes two BFS trees representing adjacent phases in a Loopover solve, as well as a threshold T. It iterates over every RxC loopover scramble that would take >T moves to solve if the default solutions provided by the BFS trees were applied. It then tries using an alternative solution for the first phase, such that the total number of moves after applying the second phase become <=T. Alternative solutions for the first phase are tried in increasing order of move count.

The class also applies a symmetry reduction beforehand to reduce the number of scrambles that must be considered. For some schemes, such as "11111x11111"-->"01011x01011"-->"00011x00011", this reduces the number of scrambles by about 8 times.

During the algorithm, if certain scrambles have taken too many failed attempts to solve, then a meet-in-the-middle brute-force algorithm is applied instead: here, a partial BFS tree of the entire space of all scrambles is precomputed, and for each scramble to solve, move sequences of increasing length are applied to the scramble via iterated DFS until the scramble becomes a scramble that appeared in the partial BFS tree.

A very old version of this class, ``LoopoverBruteForce``, was slower and much more restrictive on what kinds of solutions could be found for scrambles that would takes >T moves to solve using the default BFS solutions.

## Known Results

4x4: [GN is 18](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/#post-1444389), found by Tomasz Rokicki using a coset solver.

5x5: GN is between 22 and 42.
- The lower bound is by [a generating function argument due to xyzzy](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/#post-1333877).
- The upper bound splits the solving into 4 phases: "11111x11111"-->"01011x01011"-->"00011x00011"-->"00001x00001"-->"00000x00000". [The first two phases have a combined GN of at most 17](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/page-2#post-1447140); the [last two phases have a combined GN of at most 25](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/page-2#post-1476279) (this is actually optimal if we are only allowed to move the last two rows and last two columns (i.e. we are not allowed to temporarily disrupt the solved 3x3 region; see [here](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/page-2#post-1474968))).

6x6: GN is between 36 and 88.
- The lower bound is from the scramble consisting of moving all rows 3 units right, followed by moving all columns 3 units down; by a Manhattan distance argument, this scramble must require 36 moves to solve.
- The upper bound splits the solving into the phases "111111x111111"-->"010111x010111"-->"010101x010101"-->"000101x000101"-->"000001x000001"-->"000000x000000". [The first two phases have a combined GN of at most 22](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/page-2#post-1476279); [the last three phases each have a GN of 19, 23, and 24, respectively](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/page-2#post-1475711).
