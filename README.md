# Loopover-Brute-Force-and-Improvement
Improved brute force algorithm for optimally building any solved pseudo-rectangle on a Loopover board with an already solved pseudo-rectangle or a board with no solved pseudo-rectangle.  
A pseudo-rectangle is any region that is the intersection of the union of some rows with the union of some columns.
ex.the region below is a pseudo-rectangle because it is the intersection of the 2nd and 5th rows with the 2nd, 3rd, and 5th columns.
```
00000  
0xx0x  
00000  
00000  
0xx0x
```
Every Loopover board can be solved in phases of building progressively larger pseudo-rectangles (this is the block-building approach), and these phases can give upper bounds on the God's number of a given board.  
Given two consecutive phases of solving a board, where the first extends pseudo-rectangle A to B, and the second extends B to C, the God's number of extending from A to C can be improved beyond the sum of the God's number of both stages, by generating all scrambles that take a certain number of moves or more to extend the solved region A to C and exploting the symmetry of the board (ex. using translational symmetry to try building the pseudo-rectangles from a different location of the board) to reduce the number of moves.  
Given one phase, some of its scrambles can be avoided entirely by resorting to solving a translated version of the intended pseudo-block using fewer moves. This only works if the phase extends the null pseudo-rectangle (meaning no region is solved) to a bigger pseudo-rectangle.
