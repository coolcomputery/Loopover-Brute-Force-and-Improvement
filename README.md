# Loopover-Brute-Force-and-Improvement

This program is intended to take a block-building approach to solving Loopover (originally created by carykh) and exploit the symmetries of the puzzle to improve the upper bounds on God's number for Loopover.

## Formal explanation

A RxC Loopover is a grid of cells with R rows and C columns, where each row and column can be slided, and each cell has a unique number (see https://loopover.gitlab.io/). The objective is to take a loopover with the numbers scrambled and slide them back into the solved order. Here rows will be indexed from 0 to R-1 (top-to-bottom), and columns will be indexed from 0 to C-1 (left-to-right).

A (R,C,lr,lc) loopover, where lr and lc are sets of numbers, is a RxC loopover but with every row with its index in lr and every column with its index in lc being locked (unable to move). For example, a (4,4,[0,1],[0,2]) loopover is a 4x4 loopover but with rows 0 and 1 locked and columns 0 and 2 unable to move. The below grid shows the places that cannot move as a result of these restrictions, which will be called "locked cells", as "x"s:

```
x.x.  
x.x.  
....  
....
```

A (R,C,lr,lc,wr,wc) tree is an object that takes any (R,C,lr,lc) loopover with all its locked cells solved and expands the region of solved cells. More formally, it shifts the rows and columns that are able to move, such that every cell with its row index in the set union(lr,wr) and its column index in the set union(lc,wc) is solved. For example, the (4,4,[0,1],[0,2],[2],[3]) takes a (4,4,[0,1],[0,2]) loopover with all its locked cells solved and expands the solved region into the set of locked cells of the (4,4,[0,1,2],[0,2,3]) loopover.
```
x.x.  
x.x.  
....  
....  
becomes  
x.x*  
x.x*  
*.**  
....  
(newly solved cells are marked with "*")
```

The tree expands the region of solved cells using as few moves as possible. To do this, it performs a breadth-first search from the goal (where all cells in the row set union(lr,wr) and column set union(lc,wc) are solved) to all possible permutations of the (R,C,lr,lc) loopover, but only paying attention to the cells that will become newly solved.

Any RxC loopover can be solved by applying one or more trees onto it, progressively solving larger and larger regions of it (this is called block-building), and this gives an upper bound on the fewest possible moves needed to solve the original RxC loopover.

The program ``LoopoverBFSLarge.java`` creates this BFS tree for up to a few billion permutations by mapping each permutation to a number, converting it into backwards base 95 (to be efficient in memory), and writing it into onw of several files. Each file tells how deep that permutation is in the BFS. However, it cannot store the actual tree (what the parent permutation of each permutation is).

The program ``LoopoverBruteForce.java`` takes two BFS trees that intended to be used consecutively during an actual solve of a Loopover scramble. It then generates all RxC loopover permutations that take at least a certain threshold number of moves to solve, and sees if adding some arbitrary moves before using the same block-building strategy will reduce the total number of moves.

If applicable, it will also first check if a transformed version of the permutation can be solved in fewer moves. The transformation must be such that this new set of moves can be converted into moves that solve the original loopover.
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

<sup>1</sup>this program uses transpositions combined with reflections, which allows it to create rotations (transposition+reflection)
