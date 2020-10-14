## About:
main.cpp aims to calculate the allocation and payment outcome,
for combinatorial auctions given the bids as input.

implemented functions: 
- winner determination 
- core allocation (LP/brute force)
- payment functions: 
    - first-price
    - vcg
    - vcg nearest (QP)
    - proxy (QP)
    - proportional (limited precision binary search over LP)
- printout functions (bids, winner determination, outcomes)

## Initialization:
There's an executable (compiled main) in the repository. To compile yourself,
execute ./setup_cgal.sh to generate the Makefile, which then allows you to compile using 'make'. 
___
## Run a test:
The bids are read by standard input, using the following format:
1. first int t, the number of auctions to be run
2. int N, M, r; The number if bidders, items, and (exact) number of bids placed per bidder
> to run an example with different number of bids per players, set r to maximal number of bids per player
and add 0 bids to every player s.t. they bid on r bundles.

3. for every N*r bid: int bid value, int number of items in bundle, and one int for each item in bundle as an identifier.
The first r bids will be mapped to the first bidder and so on. 

Easiest way to run a test, is to write the bids in a file (see the .in files in testsets/), then run ./main < inputfile
___
## Notes
- Currently WD calculates one optimal allocation,
no information on which allocation is favored if there are multiple social welfare optimal ones.
- proportional payment function:
     - parameter alpha is calculated to a limited precision (currently 1.0/8193, set in function called 'proportional').
