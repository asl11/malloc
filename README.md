# malloc
Explicit segregated free list implementation of malloc. Optimized to have efficient utilization of space (tries to fit all malloc requests next to eachother in the heap, after frees), 
as well as time efficiency. 

Heap stores a linked list of free lists, sorted by size. When a new free block is malloced, will check if free lists in the range of the size requested have free blocks, as well as two free lists above.
After the block is freed, it is added to the end of the heap and put back in the free list. Will coalesce freed blocks for more space, and readd them to the free list. 

mm.c is the main file
