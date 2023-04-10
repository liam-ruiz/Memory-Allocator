A memory allocator using a segregated list structure, that implements the use of malloc, realloc, and free.

There are some accompanying for the profilling of the memory allocator. 

Running mdriver.c will test the allocator on a series of trace files that simulate malloc, realloc, and free calls and 
document their throughput and peak memory utilization. Adding the -v option when running mdriver.c will give a breakdown 
for each trace. 

This was run on a centralized remote Unix device and achieved the maximum throughput.



