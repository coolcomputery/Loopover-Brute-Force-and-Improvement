# Loopover-Brute-Force-and-Improvement

This program is intended to take a block-building approach to solving Loopover (originally created by carykh) and exploit the symmetries of the puzzle to improve the upper bounds on God's number for Loopover.

## Formal explanation

A RxC Loopover is a grid of cells with R rows and C columns, where each row and column can be slided, and each cell has a unique number (see https://loopover.gitlab.io/). The objective is to take a loopover with the numbers scrambled and slide them back into the solved order. Here rows will be indexed from 0 to R-1 (top-to-bottom), and columns will be indexed from 0 to C-1 (left-to-right).

A RxC Loopover in the state (lr,lc), where lr and lc are binary strings of lengths R and C respectively, is a RxC loopover but with row r locked if lr[r]==0 and column c locked if lr[c]==0. Thus, every piece (r,c) s.t. lr[r]==0 and lc[c]==0 is locked, i.e. it cannot be moved. For example, a 4x4 Loopover in the state (0011,0101) looks like the following, where each locked piece is marked with an "x":

```
x.x.  
x.x.  
....  
....
```

A tree over a RxC Loopover uses BFS to optimally solve every RxC Loopover in a starting state (lr0,lc0) to an ending state (lr1,lc1). For example, a tree over a 4x4 Loopover from (0011,0101) to (0001,0100) looks like the following, where locked pieces are marked with "x" and pieces that will be solved by the tree are marked with "'":
```
x.x.  
x.x.  
....  
....  
--> 
x.x'  
x.x'  
'.''  
....  
```

Any RxC loopover can be solved by applying one or more trees onto it, progressively solving larger and larger regions of it (this is called block-building), and this gives an upper bound on the "God's number" of RxC Loopover, i.e. the fewest moves necessary to be able to solve every scramble of RxC Loopover.

The classes ``LoopoverBruteForce.Tree`` and ``LoopoverBFS`` create these kinds of trees for up to ~100-200 million scramble. The latter notates Loopover states as (R,C,str(lr0)+"x"+str(lc0),str(lr1)+"x"+str(lc1)); for example, the tree in the previous example would be notated as (4,4,"0011x0101","0001x0100"). The former uses an older notation, where sets of numbers are used instead of binary strings to track all locked rows and columns, and only newly locked rows and columns are used to notate the ending state. For example, (4,4,"0011x0101","0001x0100") would be written as (4,4,[0,1],[0,2],[2],[3]).

The class ``LoopoverBFSLarge`` creates these BFS trees for up to a few billion scramble, writing all scrambles onto several files, separated by each scramble's depth in the BFS tree. However, it cannot store the actual tree (what the parent scramble of each scramble is).

The class ``LoopoverBFSImprove`` takes two BFS trees that intended to be used consecutively during an actual solve of a Loopover scramble. It then generates all RxC loopover permutations that take at least a certain threshold number of moves to solve, and sees if adding some arbitrary prefix moves before using the same block-building strategy will reduce the total number of moves.

If the start state of the first of the two BFS trees has all rows and all columns free, and the end state of the second of the two BFS trees has all rows and all columns locked, then an older version of this class, ``LoopoverBruteForce``, will do what ``LoopoverBFSImprove`` does but also check if a transformed version of the scramble can be solved in fewer moves. The transformation must be such that this new set of moves can be converted into moves that solve the original loopover.
For example, the trees (4,4,[],[],[0,1],[0,1,2]) and (4,4,[0,1],[0,1,2],[2,3],[3]) solve a RxC loopover as follows ("x" denotes regions that are locked, and therefore necessarily solved):
```
....  
....  
....  
....  
->  
xxx.  
xxx.  
....  
....  
->  
xxxx  
xxxx  
xxxx  
xxxx (entire board solved)
```

If we want to reduce the number of moves it takes to solve this RxC loopover subgroup, for each scramble that takes >=D moves to solve with the naive block-building procedure for some number D, we can first add a prefix move to the scramble before doing the block-building.

If the end result of the block-building is the entire Loopover board being solved, another method is to solve transformed versions of the intended regions we want to solve instead of restricting ourselves to start at the top-left corner, such as translations, ex.
```
....  
....  
....  
....  
->  
....  
xxx.  
xxx.  
....  
->  
xxxx  
xxxx  
xxxx  
xxxx
```

Other possible transformations include rotations<sup>1</sup> and reflections, ex.
```
....  
....  
....  
....  
->  
xx..  
xx..  
xx..  
....  
->  
xxxx  
xxxx  
xxxx  
xxxx
```

<sup>1</sup>the class ``LoopoverBruteForce`` uses transpositions combined with reflections, which allows it to create rotations (transposition+reflection)
