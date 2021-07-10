# Loopover-Brute-Force-and-Improvement

This program is intended to take a block-building approach to solving Loopover (originally created by carykh) and exploit the symmetries of the puzzle to improve the upper bounds on God's number for Loopover.

NRG version: https://github.com/coolcomputery/Loopover-NRG-Upper-Bounds

## Formal explanation

### BFS Tree

A RxC Loopover is a grid of cells with R rows and C columns, where each row and column can be slided, and each cell has a unique number (see https://loopover.gitlab.io/). The objective is to take a loopover with the numbers scrambled and slide them back into the solved order. Here rows will be indexed from 0 to R-1 (top-to-bottom), and columns will be indexed from 0 to C-1 (left-to-right).

A RxC Loopover in the state (lr,lc), where lr and lc are binary strings of lengths R and C respectively, is a RxC loopover but with row r locked if lr[r]==0 and column c locked if lr[c]==0. Thus, every piece (r,c) s.t. lr[r]==0 and lc[c]==0 is locked, i.e. it cannot be moved. For example, a 4x4 Loopover in the state (0011,0101) looks like the following, where each locked piece is marked with an "x":

```
x.x.  
x.x.  
....  
....
```

A tree over a RxC Loopover uses BFS to optimally solve every RxC Loopover in a starting state (lr0,lc0) to an ending state (lr1,lc1). For example, a tree over a 4x4 Loopover from (0011,0101) to (0001,0100) will extend a solved block of the board, as shown below:
```
x.x.     x.xx  
x.x. --> x.xx  
....     x.xx  
....     ....  
```

Any RxC loopover can be solved by applying one or more trees onto it, progressively solving larger and larger regions of it (this is called block-building), and this gives an upper bound on the "God's number" of RxC Loopover, i.e. the fewest moves necessary to be able to solve every scramble of RxC Loopover.

The classes ``LoopoverBruteForce.Tree`` and ``LoopoverBFS`` create these kinds of trees for up to ~100-200 million scramble. The latter notates Loopover states as (R,C,str(lr0)+"x"+str(lc0),str(lr1)+"x"+str(lc1)); for example, the tree in the previous example would be notated as (4,4,"0011x0101","0001x0100"). The former uses an older notation, where sets of numbers are used instead of binary strings to track all locked rows and columns, and only newly locked rows and columns are used to notate the ending state. For example, (4,4,"0011x0101","0001x0100") would be written as (4,4,[0,1],[0,2],[2],[3]).

The class ``LoopoverBFSLarge`` creates these BFS trees for up to a few billion scramble, writing all scrambles onto several files, separated by each scramble's depth in the BFS tree. However, it cannot store the actual tree (what the parent scramble of each scramble is).

### BFS Improvement

The class ``LoopoverBFSImprove`` takes two BFS trees that intended to be used consecutively during an actual solve of a Loopover scramble. It then generates all RxC loopover permutations that take at least a certain threshold number of moves to solve if the two trees were applied naively, and sees if solving the pieces in a different 2-phase block-building fashion and/or adding some arbitrary prefix moves will reduce the total number of moves. For example, if there were the trees (5,5,"11111x11111","00111x00111"), (5,5,"00111x00111","00011x00011"), then the class could try solving a given scramble as "11111x11111"-->"10011x00111"-->"00011x00011" or as "11111x11111"-->"01011x01011"-->"00011x00011" instead of only solving it in the default method ("11111x11111"-->"00111x00111"-->"00011x00011").

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

An older version of this class, ``LoopoverBruteForce``, was more restrictive on using different 2-phase block-building solving methods, but allowed solving reflected versions of scrambles, in the special case that the first of the two BFS trees has all rows and all columns free, and the end state of the second of the two BFS trees has all rows and all columns locked. However, this extra feature is only for very small Loopover boards, such as [4x4, whose God's number is already solved (the number is 18)](https://www.speedsolving.com/threads/loopover-gods-number-upper-bounds-4%C3%974-asymptotics-etc.75180/#post-1444389), and the class is much slower than ``LoopoverBFSImprove``.
