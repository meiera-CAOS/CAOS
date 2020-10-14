#include <CGAL/QP_models.h>
#include <CGAL/QP_functions.h>
#include <CGAL/Gmpz.h>
#include <CGAL/Quotient.h>
#include <cassert>
#include <vector>
#include <set>
#include <map>
#include <utility>
#include <iterator>

// choose input type (input coefficients must fit)
typedef int IT;
typedef double DT;
typedef int ETZ;
typedef CGAL::Gmpq ETQ;
typedef CGAL::Quotient<ETQ> Q;

// program and solution types
typedef CGAL::Quadratic_program<IT> IntegerProgram;
typedef CGAL::Quadratic_program<DT> DoubleProgram;
typedef CGAL::Quadratic_program_solution<ETZ> AllocSolution; //maybe just int type
typedef CGAL::Quadratic_program_solution<ETQ> CoreSolution;

typedef std::map<int, int> Mp;
typedef std::set<int> S;
typedef std::pair<int,S> BP; //a bid first bid, second bundle bid on
typedef std::vector<BP> VP;
typedef std::vector<VP> VVP; //vector of N bidders, with r bids as
typedef std::vector<int> VI;
typedef std::pair<int, VI> SP; // wd value and vector of allocation outcome
typedef std::vector<SP> VSP; // vector of precomputed WD allocations
typedef std::vector<Q> VQ;
typedef std::pair<Q, VQ> SPQ; // double precision sol value and vector of alloc outcome

struct outcome{int player; S bundle; Q price;};
typedef std::vector<outcome> VO; //vector of outcomes: of winning bidders, allocated bundle, payment

struct allocation{int sw; S bids; S items;};//sum of alloc bids, bid id's that are alloc, sold items

//GLOBAL VARS
bool debug = true;
int N, M, r;
VVP bids;

void printBids(VVP &bids){
    std::cout << "bids [[player_i's r bids(bid_value, {items bid on})*r]*N]:\n[";
    for(int i = 0; i < N; i++) {
        std::cout << "[";
        for(int j = 0; j < r; j++){
            std::cout << "(" << bids.at(i).at(j).first << ", {";
            for(auto it = bids.at(i).at(j).second.begin(); it != bids.at(i).at(j).second.end();){
                std::cout << *it;
                if(++it != bids.at(i).at(j).second.end()){
                    std::cout  << ", ";
                } else std::cout << "})";
            }
            if(j < r-1){
                std::cout  << ", ";
            }
        }
        (i < N-1) ? std::cout << "], " : std::cout << "]";
    }std::cout << "]\n";
}

void printWD(SP &sol){
    std::cout << "winner determination: sum of winning bids | allocation vector: \n";
    std::cout << sol.first << " | (";
    for(int a: sol.second) std::cout << a << ", ";
    std::cout << ")\n";
}

void printOutcome(VO &outV, std::string pF){
    double SW = 0.0;
    std::cout << pF << " outcome [(winning bidder, {wins items}, payment)]:\n[";
    for(outcome a : outV){
        SW += CGAL::to_double(a.price);
        std::cout << "(" << a.player << ", {";
        for(int b : a.bundle){
            std::cout << b << ", ";
        }std::cout << "}, " << a.price << "), ";
    }std::cout << "]\n";
    std::cout << pF << " SW = " << SW << "\n";
}

int cIDallOtherPlayers(int i){
    assert(i < N);
    return ((1<<N) -1 -(1<<i));
}

Mp cIDmapPlayers(int cID){
    //map idx in C to idx in N
    int res = 0;
    Mp cIDmap;
    for(int i = 0; i < N; i++) if(cID & 1<<i){
        cIDmap.emplace(res, i);
        res++;
    }
    assert(cIDmap.size() == res);
    return cIDmap;
}

void back_track(int idx, int idxBound, allocation &currA, allocation &maxA, Mp &cIDmap){
    if(idx < idxBound){//construct possible assignment
        for(int j = 0; j <= r; j++){//pick one possible winning bid
            if(j==r){//no bid allocated of player idx if j == r
                back_track(idx+1, idxBound, currA, maxA, cIDmap);
            }
            else{//check if bid j of player idx can be added
                bool conflict = false;
                assert(j < r);
                for(int a : bids.at(cIDmap.at(idx)).at(j).second){
                    if(currA.items.find(a) != currA.items.end()){//item already allocated
                        conflict = true;
                        break;
                    }
                }
                if(!conflict){//allocate bid
                    currA.sw += bids.at(cIDmap.at(idx)).at(j).first;
                    currA.bids.insert(cIDmap.at(idx)*r+j);
                    for(int a : bids.at(cIDmap.at(idx)).at(j).second){
                        currA.items.insert(a);
                    }
                    back_track(idx+1, idxBound, currA, maxA, cIDmap);
                    currA.sw -= bids.at(cIDmap.at(idx)).at(j).first;
                    assert(currA.sw >= 0);
                    assert(currA.bids.find(cIDmap.at(idx)*r+j) != currA.bids.end());
                    currA.bids.erase(cIDmap.at(idx)*r+j);
                    for(int a : bids.at(cIDmap.at(idx)).at(j).second){
                        assert(currA.items.find(a) != currA.items.end());
                        currA.items.erase(a);
                    }
                }
            }
        }
    }
    else{//check if maximal assignment
        if(currA.sw > maxA.sw) maxA = currA;
    }
}

SP WD_backtrack(int cID){
    // map cID to set of participating players (from N to N')
    Mp cIDmap = cIDmapPlayers(cID);
    int numP = cIDmap.size();
    // for participating players, try all feasible combinations,
    // no winning bid, or one of the bids winning - if feasible with partial solution
    // keep max and assignment of max
    // feasible: (every item sold at most once, every player wins at most once)
    S bds, itms;
    allocation zeroA{0, bds, itms};
    allocation maxA{0, bds, itms};
    back_track(0, numP, zeroA, maxA, cIDmap);
    /*
    if(debug){
        std::cout << "wd BF max allocation of value: " << maxA.sw << ", allocates: (";
        for(int a : maxA.bids) std::cout << a << ", ";
        std::cout << ")\n";
    }
    */
    // map result N'*r back to assignment over N*r bids
    SP sol;
    sol.first = maxA.sw;
    for(int i = 0; i < N*r; i++){
        if(!maxA.bids.empty() and *maxA.bids.begin() == i){//allocated
            sol.second.push_back(1);
            maxA.bids.erase(i);
        }
        else sol.second.push_back(0);
    }
    return sol;
}

SP WD(int cID = -1){// N bidders, M items, r bids per bidder
    if(cID == -1) cID = (1<<N) -1; //every player in set
    //could be nicely solved using binary programming

    //only consider bids from players within coalitionID (binary: 1 at position of player in bitstring coalitionID)
    //keeping output allocation over all N*r bids

    // create an LP with Ax <= b, lower bound 0 and no upper bounds
    IntegerProgram lp (CGAL::SMALLER, true, 0, true, 1);

    // set the conditions that only one bid per player (of coalition) can be winning
    for(int i = 0; i < N; ++i) {
        // if i not in coalition skip
        if((1<<i & cID)){//check if part of coalition
            lp.set_b(i, 1);
        } else {
            lp.set_b(i, 0);
        }
        for (int j = 0; j < r; ++j) {
            lp.set_a(i*r+j, i, 1); //one variable per bid, one equation per bidder, allocation
            // (variable id, ineq id, var value)
        }
    }

    for(int i = N; i < N+M; i++){// every item sold at most once
        lp.set_b(i, 1);
    }
    for(int i = 0; i < N; ++i){
        for(int j = 0; j < r ; ++j) {
            for(int a: bids.at(i).at(j).second){
                lp.set_a(i*r+j, N+a, 1); // bundle of bid i*r+j contains item a
            }
        }
    }

    // objective function
    for(int i = 0; i < N; ++i){
        // if i not in coalition skip
        for(int j = 0; j < r; ++j){
            if(1<<i & cID){ //maximize social welfare of coalition members
                lp.set_c(i*r+j, -bids.at(i).at(j).first);
            }
        }
    }

    // solve the program, using ET as the exact type
    AllocSolution s = CGAL::solve_linear_program(lp, ETZ());
    assert(s.solves_linear_program(lp));
    assert(!s.is_infeasible());

    //check that LP solved in binary fashion (workaround) - should use binary program instead
    bool correct = true;
    for(auto it = s.variable_values_begin(); it != s.variable_values_end(); ++it){
        if((int)(*it).numerator() != 0){
            assert((*it).numerator() <= (*it).denominator());
            if((*it).numerator() < (*it).denominator()){
                correct = false;
                break;
            }
        }
    }

    // output solution
    SP sol;
    if(correct){
        // division here is not lossy if proper solution found
        sol.first = -((int)s.objective_value().numerator())/(int)s.objective_value().denominator();
        for(auto it = s.variable_values_begin(); it != s.variable_values_end(); ++it){
            sol.second.push_back((int)(*it).numerator()/(int)(*it).denominator());
        }
    }
    else{
        sol = WD_backtrack(cID);
    }
    return sol;
}

VSP precomputeWD(){
    VSP solV;
    for(int i = 0; i < 1<<N; i++){
        SP sol = WD(i);
        solV.push_back(sol);
    }
    assert (solV.size()==1<<N);
    return solV;
}

VO firstPrice(SP &alloc){
    VO sol;
    //auto it = alloc.second.begin();
    assert(alloc.second.size() == N*r);
    for(int i = 0; i < N; i++){
        for(int j = 0; j < r; j++){
            if(alloc.second.at(i*r+j)){
                sol.push_back(outcome{i, bids.at(i).at(j).second, (Q)bids.at(i).at(j).first});
            }
        }
    }
    printOutcome(sol, "first price");
    return sol;
}

VO vcg(SP &alloc, VSP &wdV){
    VO sol;
    assert(alloc.second.size() == N*r);
    for(int i = 0; i < N; i++){
        for(int j = 0; j < r; j++){
            if(alloc.second.at(i*r+j)){
                int cID = cIDallOtherPlayers(i);
                int price = wdV.at(cID).first - alloc.first + bids.at(i).at(j).first;
                sol.push_back(outcome{i, bids.at(i).at(j).second, (Q)price});
            }
        }
    }
    printOutcome(sol, "VCG payment");
    return sol;
}

std::pair<DoubleProgram, int> coreLP(SP &alloc, VSP &wdV, double alpha = 1){
    // geq wd(coalition).first - sum of "winning" bids in coalition
    // $$\sum_{j\in W \setminus C} p_j \geq wd(C) - \sum_{j\in C} b_j\cdot x_j \qquad for x given WD(b)$$

    // one core constraint for every subset C of N
    // the payment p_i (linked to every bid) are the variables of the core lp. - remodel from currently item prices are variables.
    // calc WD for every subset C of N, and the sum of allocated bids within C (allocation from WD over all N)

    DoubleProgram lp (CGAL::LARGER, true, 0, false, 0);
    int allocVar;
    int numC = 1<<N;
    for(int c = 0; c < numC; c++){// might be problematic (overflow and slow) for large N
        //SP cAlloc = WD(c);//TODO: could precompute WD for every possible C and lookup
        SP cAlloc = wdV.at(c);
        int cWinBids = 0;
        for(int i = 0; i < N; i++){
            if (!(c & 1<<i)){//player i not in coalition
            //check if player i won a bundle
                for(int a = r*i; a < r*(i+1); a++){
                    lp.set_a(a, c, 1);//variable a, constraint c (bids of player i)
                }
            }
            else {// i in coalition
                // check if i won within coalition
                for (int a = r * i; a < r * (i + 1); a++) {//build sum of bids
                    if (alloc.second.at(a)) {//if winning bid in cAlloc
                        cWinBids += bids.at(i).at(a-r*i).first;// a - r*j returns # of bid
                        break;
                    }
                }
            }
        }
        int cVal = cAlloc.first - cWinBids;
        lp.set_b(c, cVal);
        // set / sum variables (initially winning players not in coalition)
    }

    // set constraint that non allocated payments are zero
    for(int i = 0; i < N*r; i++){
        if(!(alloc.second.at(i))){
            lp.set_a(i, numC, -1);
        }
    }
    lp.set_b(numC, 0);

    //set constrains that winning allocations are leq bid
    int ct = 0;
    for(int i = 0; i < N; i++){
        for(int j = 0; j < r; j++){
            if(alloc.second.at(i*r+j)){
                ct++;
                lp.set_a(i*r+j, numC + ct, -1);
                lp.set_b(numC + ct, -((double)bids.at(i).at(j).first)*alpha);
            }
        }
    }
    int numIneq = numC + ct;
    return std::make_pair(lp, numIneq);
}

VO coreAllocToPayment(SP & alloc, CoreSolution &sol){
    SPQ solPair;
    //solPair.first = 0;
    for(auto it = sol.variable_values_begin(); it != sol.variable_values_end(); ++it){
        //solPair.second.push_back(it->normalize());// type error
        solPair.second.push_back(*it);
    }
    VO solOutcome;
    for(int i = 0; i < N; i++){
        for(int j = 0; j < r; j++){
            Q price;
            if(alloc.second.at(i*r+j)){
                price = solPair.second.at(i*r+j);
                //solPair.first += price; //quotient addition ok?
                solOutcome.push_back(outcome{i, bids.at(i).at(j).second, price});
            }
            else{
                assert(solPair.second.at(i*r+j) == 0);
            }
        }
    }
    return solOutcome;
}

VO proxy(SP & alloc, DoubleProgram core){
    //using quadratic programming, could probably project it down to LP
    for(int i = 0; i < N*r; i++){
        core.set_d(i, i, 2);
    }
    CoreSolution s = CGAL::solve_quadratic_program(core, ETQ());
    assert(s.solves_quadratic_program(core));
    assert(!s.is_infeasible());
    VO proxyOut = coreAllocToPayment(alloc, s);
    printOutcome(proxyOut, "proxy payment");
    return proxyOut;
}

double minRevenueCore(DoubleProgram core, SP &alloc){
    for(int i = 0; i < N; i++){
        for(int j = 0; j < r; j++){
            core.set_c(i*r+j, 1);
        }
    }
    CoreSolution s = CGAL::solve_quadratic_program(core, ETQ());
    assert(s.solves_quadratic_program(core));
    assert(!s.is_infeasible());
    double minRev = CGAL::to_double(s.objective_value_numerator()/s.objective_value_denominator());
    return minRev;
}

VO vcg_nearest(SP & alloc, DoubleProgram core, int numIneq, VO &vcgPayment){
    //add min rev constraint, at numC + ct + 1 (what's ct)
    double minRev = minRevenueCore(core, alloc);
    int constraintIdx = numIneq +1;
    for(int i = 0; i < N*r; i++) if(alloc.second.at(i)) core.set_a(i, constraintIdx, 1);
    core.set_b(constraintIdx, minRev);
    core.set_r(constraintIdx, CGAL::EQUAL);

    //using quadratic programming, for winning bids, minimize the distance to vcg prize
    for(int i = 0; i < N*r; i++){
        if(alloc.second.at(i)) core.set_d(i, i, 2);//every item in bundle squared
    }

    for(outcome o : vcgPayment){
        //find winning bid of player o.player
        int bidID = o.player*r;
        bool found = false;
        int i = bidID;
        for(; i < (o.player+1)*r; ++i){
            if(alloc.second.at(i)){
                found = true;
                break;
            }
        }
        assert(found);
        core.set_c(i, -2*CGAL::to_double(o.price));
    }
    CoreSolution s = CGAL::solve_quadratic_program(core, ETQ());
    assert(s.solves_quadratic_program(core));
    assert(!s.is_infeasible());
    assert(s.is_optimal());
    VO vcgN_out = coreAllocToPayment(alloc, s);
    printOutcome(vcgN_out, "vcg-nearest payment");
    return vcgN_out;
}

bool alphaFeasible(SP &alloc, VSP &wdV, double alpha){//or infeasible?
    DoubleProgram core = coreLP(alloc,wdV, alpha).first;
    CoreSolution s = CGAL::solve_quadratic_program(core, ETQ());
    assert(s.solves_quadratic_program(core));
    return !s.is_infeasible();
}

VO returnProportional(SP &alloc, VSP &wdV, VO firstPriceOut, double alpha){
    DoubleProgram zeroCore = coreLP(alloc, wdV, alpha).first;
    CoreSolution s = CGAL::solve_quadratic_program(zeroCore, ETQ());
    assert(s.solves_quadratic_program(zeroCore));
    assert(!s.is_infeasible());
    VO proportional_out;  outcome po;
    for(outcome o : firstPriceOut){
        po.player = o.player;
        po.bundle = o.bundle;
        po.price = o.price * alpha;
        proportional_out.push_back(po);
    }
    printOutcome(proportional_out, "proportional payment");
    std::cout << "proportional factor alpha: " << alpha << "\n";
    return proportional_out;
}

VO proportional(SP &alloc, VSP &wdV, VO &firstPriceOut){
    //could have found set of most constraining constraints to directly deduct factor?
    //use quotient type to increase precision?
    double precision = 1.0/8193; //to stop bin search for alpha. diff than power of 2
    if(alphaFeasible(alloc, wdV, 0.0)){
        VO prop_out = returnProportional(alloc, wdV, firstPriceOut, 0.0);
        return prop_out;
    }
    //Do exp start
    assert(alphaFeasible(alloc, wdV, 1.0));
    double prev = 1.0, alpha = 0.5;
    while(alpha >= precision && alphaFeasible(alloc, wdV, alpha)){
        prev = alpha;
        alpha /= 2.0;
    }
    if(alpha < precision){
        VO proportional_out = returnProportional(alloc, wdV, firstPriceOut, prev);
        return proportional_out;
    }
    assert(alphaFeasible(alloc, wdV, prev));
    assert(!alphaFeasible(alloc, wdV, alpha));
    //Bin search- stop when delta < precision is reached.
    while(prev-alpha > precision){
        assert(alpha < prev);
        double mean = prev - (prev-alpha)/2.0;
        if(alphaFeasible(alloc, wdV, mean)){
            prev =  mean;
        } else{
            alpha = mean+precision/2.0;
        }
        double diff = prev - alpha;
    }
    assert(alphaFeasible(alloc, wdV, prev));
    assert(!alphaFeasible(alloc, wdV, alpha-precision));

    VO proportional_out = returnProportional(alloc, wdV, firstPriceOut, prev);
    return proportional_out;
}

void testcase(){
    std::cin >> N >> M >> r;
    bids = VVP(N, VP(r));
    int bundleSize, item;
    for(int i = 0; i < N; i++) for(int j = 0; j < r; j++){
            std::cin >> bids.at(i).at(j).first >> bundleSize;
            for(int k = 0; k < bundleSize; ++k){
                std::cin >> item;
                bids.at(i).at(j).second.insert(item);
            }
        }
    if(debug){
        printBids(bids);
    }
    VSP wdV = precomputeWD();
    SP alloc = wdV.at((1<<N)-1);
    printWD(alloc);
    VO firstPricePayment = firstPrice(alloc);
    VO vcgPayment = vcg(alloc, wdV);
    DoubleProgram core; int numIneq;
    std::tie(core, numIneq) = coreLP(alloc, wdV);
    vcg_nearest(alloc, core, numIneq, vcgPayment);
    proxy(alloc, core);
    proportional(alloc, wdV, firstPricePayment);
    std::cout << "\n";
}

int main(){
    std::cout << std::setprecision(5);
    std::cout << std::fixed;
    int t; std::cin >> t;
    while(t--) testcase();
    return 0;
}
