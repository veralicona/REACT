load (getenv("ADAM_ROOT")|"superADAM/share/JSON.m2")

newPackage(
    "PolynomialDynamicalSystems",
        Version => "1.0", 
        Date => "12 May 2015",
        Authors => {
         {Name => "Brandy Stigler", Email => "bstigler@smu.edu", HomePage => "http://faculty.smu.edu/bstigler"},
         {Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => "http://www.math.cornell.edu/~mike"}
         },
        Headline => "Utilities for polynomial dynamical systems",
        PackageExports => {"Points", "JSON"},
        DebuggingMode => true
        )

export{
    "readTSDataFromJSON",
    "findPDS",
--    "gfanRevEng",
    "createRevEngJSONOutputModel",
    "getVars",
    "makeVars",
    "TimeSeriesData", 
    "FunctionData", 
    "readTSData",
    "makeTimeSeriesJSON",
    "functionData",
    "subFunctionData",
    "minRep",
    "findFunction",
    "checkFunction",
    "WildType",
    "Avoid",
    "Output"
    }
    
debug Core
support ZZ := (n) -> {}

---------------------------------------------------------------------------------------------------
-- Declaration of new data types
---------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------
-- TimeSeriesData: This hashtable stores time series data with values in a set k.
-- The data is (txn)-dimensional, where t=#timepoints-1, n=#variables.
-- keys   = time series labels
-- values = time series
--    key = Wildtype:    value = list of (txn)-matrices of wildtype time series
--    key = (i, file_i): value = list of (txn)-matrices of time series for ith knockout 

TimeSeriesData = new Type of HashTable
 
ring(TimeSeriesData) :=  (T) -> (
    ring first flatten values T
)

numColumns(TimeSeriesData) := (T) -> (
    numColumns first flatten values T
)
---------------------------------------------------------------------------------------------------
-- FunctionData: This hashtable defines a function f:k^n->k, where k is a finite field.
-- keys   = points in k^n (in domain of f)
-- values = points in k (in codomain of f)

FunctionData = new Type of HashTable


---------------------------------------------------------------------------------------------------
-- Utilities for working with polynomial dynamical systems
---------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------
-- Given an integer n, makeVars returns a list of n variables of type xi.

makeVars = method(TypicalValue => List)
makeVars(ZZ) := (n) -> apply(1..n, i -> value ("x"|i))

---------------------------------------------------------------------------------------------------
-- Given an element of a polynomial ring, getVars returns the list of variables in the polynomial.

getVars = method(TypicalValue => List)
getVars(ZZ) := (n) -> ({})
getVars(RingElement) := (f) -> (
    -- standard form of the monomials of f, i.e., no coefficients
    SF := apply(terms f, m -> first keys standardForm m);
    Vars := {};
    select(SF, h->if keys h!={} then Vars=append(Vars, keys h));
    Vars = sort unique flatten Vars;
    apply(Vars, e->e+1)
)

---------------------------------------------------------------------------------------------------
-- Given a list of elements, see prints out each element on a single line, followed by a hard return.

see = method()
see(List) := (fs) -> scan(fs, (g -> (print g; print "")))


---------------------------------------------------------------------------------------------------
-- Utilities for data processing
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- Given a list of wildtype and a list of knockout time series data files, as well as a coefficient ring,
-- readTSData returns a TimeSeriesData hashtable of the data.
-- Uses "readMat"

createRevEngJSONOutputModel = method()
createRevEngJSONOutputModel ErrorPacket := (E) -> E
createRevEngJSONOutputModel List := (L) -> (
    -- Better have at least one variable
    -- MES: currently, input is expected to be a list of polynomials
    assert(#L > 0);
    R := ring L#0#0#0;
    toHashTable {
        "type"=>"model",
        "numberVariables" => numgens R,
        "fieldCardinality" => char R,
        "updateRules" => new Array from for i from 0 to numgens R - 1 list (
            { 
                "target" => toString R_i,
                "functions" => new Array from for j from 0 to #L_i-1 list(
                    {
                            "inputVariables"=>apply(new Array from support L#i#j#0, toString),
                            "polynomialFunction"=>toString L#i#j#0,
				            "score"=>L#i#j#1
                    }
                    )
            }
        )})

readTSDataFromJSON = method(TypicalValue=>TimeSeriesData)
 -- input argument follows description in doc/json-standard-formats.txt
readTSDataFromJSON String := (jsonInput) -> (
    -- TODO: return an error packet if the data is missing fields (i.e. don't do M2 error).
    data := parseJSON jsonInput;
    if not instance(data, HashTable) or not data#?"type" or data#"type" != "timeSeries" then 
    return errorPacket "in readTSDataFromJSON: input is not time series data";
    -- if there is no error, we get here, and construct a TimeSeriesData
    n := data#"numberVariables";
    p := data#"fieldCardinality";
    kk := if p==0 then RR else ZZ/p;
    -- Now create the TimeSeriesData from the wildtype and knockout data
    ts := data#"timeSeriesData"; -- list of hashtables, each has a matrix, and index (knockout list)
    matrices := new MutableHashTable;
    for experiment in ts do (
        ind := experiment#"index";
        typ := if #ind == 0 then WildType else ind#0;
        mat := matrix(kk, experiment#"matrix");
        if matrices#?typ then 
            matrices#typ = append(matrices#typ, mat)
        else
            matrices#typ = {mat};
        );
    new TimeSeriesData from matrices
)

makeTimeSeriesJSON = method()
-- version for taking data from files
--makeTimeSeriesJSON(String, ZZ, ZZ, List) := (description, prime, numvars, experiments) -> (
--    kk := ZZ/prime;
--    R := kk[makeVars numvars];
--    timeSeriesData := for e in experiments list (
--        new HashTable from {
--        "index" => e#0,
--        "matrix" => entries readMat(e#1, ZZ)
--       });
--    vals := {};
--    for t in timeSeriesData do vals = unique join(vals, unique flatten t#"matrix");
--    if any(vals, v -> v < 0 or v >= prime) then 
--    error "data not in range 0..prime-1";
--    prettyPrintJSON new HashTable from {
--        "description" => description,
--       "type" => "timeSeries",
--        "fieldCardinality" => prime,
--        "numberVariables" => numvars,
--        "timeSeriesData" => timeSeriesData
--        }
--    )

--version for taking data from memory
--experiments is a list {{index set,matrix},{index set,matrix},...} of pairs in which 
--if index set={}, then  matrix corresponds to data from a WT experiment
--if index set={i,j,...}, then  matrix corresponds to data from an experiment in which nodes i, j,... have been knocked out
--and matrix is a double list (not an M2 matrix)
makeTimeSeriesJSON(String, ZZ, ZZ, List) := (description, prime, numvars, experiments) -> (
    kk := ZZ/prime;
    R := kk[makeVars numvars];
    timeSeriesData := for e in experiments list (
        new HashTable from {
        "index" => e#0,
        "matrix" => e#1
        });
    vals := {};
    for t in timeSeriesData do vals = unique join(vals, unique flatten t#"matrix");
    if any(vals, v -> v < 0 or v >= prime) then 
    error "data not in range 0..prime-1";
    prettyPrintJSON new HashTable from {
        "description" => description,
        "type" => "timeSeries",
        "fieldCardinality" => prime,
        "numberVariables" => numvars,
        "timeSeriesData" => timeSeriesData
        }
    )


findPDS = method(TypicalValue=>List)
findPDS(TimeSeriesData) := (T) -> (
    kk := ring T;
    n := numColumns T;
    R := kk[makeVars n];
    FD := apply(n, i->functionData(T,i+1));
    errorPos := position(FD, f -> instance(f, ErrorPacket));
    if errorPos =!= null then 
        FD#errorPos -- returns an ErrorPacket for first error found.
    else (
        Fs := apply(n, i -> findFunction(FD_i,gens R));
        for f in Fs list {{f,1.0}}
        )
)
findPDS(ErrorPacket) := (E) -> E

---------------------------------------------------------------------------------------------------
mesintersect = (L) -> (
     -- L is a list of monomial ideals
    M := L#0;
    R := ring M;
    i := 1;
    << #L << " generators" << endl;
    while i < #L do (
     << "doing " << i << endl;
     M = newMonomialIdeal(R, rawIntersect(raw M, raw L#i));
     i = i+1;
     );
    M)

mesdual = method()

-- TODO: use Macaulay2 "dual MonomialIdeal", as that uses Roune's 
--   optimized algorithm
mesdual MonomialIdeal := (J) -> (if J == 0 
  then monomialIdeal 1_(ring J) 
  else if ideal J == 1 then monomialIdeal 0_(ring J)
  else mesintersect (monomialIdeal @@ support \ first entries generators J))
  
displayMinRep = (fil,I) -> (
     -- show: tally of degree of min gens
     -- if any of size 1,2,3, display them
     g := flatten entries gens I;
     h := tally apply(g, f -> first degree f);
     fil << #g << " min rep elements " << h << endl;
     h1 := select(g, f -> first degree f == 1);
     h2 := select(g, f -> first degree f == 2);
     h3 := select(g, f -> first degree f == 3);
     h4 := select(g, f -> first degree f == 4);
     if #h1 > 0 then fil << "min rep length 1 = " << toString h1 << endl;
     if #h2 > 0 then fil << "min rep length 2 = " << toString h2 << endl;
     if #h3 > 0 then fil << "min rep length 3 = " << toString h3 << endl;
     if #h3 > 0 then fil << "min rep length 4 = " << toString h4 << endl;
     )

displayMinSets = (fil,J) -> (
     -- show: tally of degree of min gens
     -- if any of size 1,2,3, display them
     g := J;
     h := tally apply(g, f -> first degree f);
     fil << #g << " min set elements " << h << endl;
     hlo := min keys h;
     h1 := select(g, f -> first degree f == 1);
     h2 := select(g, f -> first degree f == 2);
     h3 := select(g, f -> first degree f == 3);
     if #h1 > 0 and #h1 < 10 then fil << "min sets length 1 = " << toString h1 << endl;
     if #h2 > 0 and #h2 < 10 then fil << "min sets length 2 = " << toString h2 << endl;
     if #h3 > 0 and #h3 < 10 then fil << "min sets length 3 = " << toString h3 << endl;
     if hlo > 3 and (true or h#hlo < 8) then (
          hhlo := select(g, f -> first degree f == hlo);
          fil << "min sets length " << hlo << " = " << netList hhlo << endl;
      );
     )

minSets = method(Options => {Output => null,
                         Avoid => null}
                 )
minSets(TimeSeriesData, ZZ, Ring) := opts -> (T, i, R) -> (
        d := functionData(T,i);
        I := minRep(d,R);
    if instance(I,ZZ) then I = monomialIdeal(0_R); -- because I can be the zero element
--    I = I + monomialIdeal(R_(i-1));
    if opts.Avoid =!= null then (
         J1:= saturate(I,product flatten {opts.Avoid});
         I = J1;
         );
    J := flatten entries gens mesdual I;
    if opts.Output =!= null
    then (
      fil := openOut opts.Output;
      displayMinRep(fil, I);
          displayMinSets(fil, J);
      close fil;
      );
    J /sort @@ support
    )

minSets(TimeSeriesData) := opts -> (T) -> (
    n:=numColumns T;
    apply(n, i->minSets(T,i+1,ring T, opts))
)
---------------------------------------------------------------------------------------------------
-- Internal to "readTSData"
-- Given a data file and a coefficient ring, readMat returns the (txn)-matrix of the data (t=time, n=vars). 

readMat = method(TypicalValue => Matrix)
readMat(String,Ring) := (filename,R) -> (
     ss := select(lines get filename, s -> length s > 0);
     matrix(R, apply(ss, s -> (t := separateRegexp(" +", s); 
                 t = apply(t,value);
                     select(t, x -> class x =!= Nothing))))
)

---------------------------------------------------------------------------------------------------
-- Given a list of wildtype and a list of knockout time series data files, as well as a coefficient ring,
-- readTSData returns a TimeSeriesData hashtable of the data.
-- Uses "readMat"

readTSData = method(TypicalValue => TimeSeriesData)
readTSData(List,List,Ring) := (wtfiles, knockouts, R) -> (
     -- wtfiles: list of file names for wild type data series
     -- knockouts: list of pairs (i,filename), where
     --  i is an integer with which node gets knocked out (first variable has index 1).
     --  filename is the corresponding time series data
     -- output: TimeSeriesData

     wtmats := apply(wtfiles, s -> readMat(s,R));
     H := new MutableHashTable;
     scan(knockouts, x -> (
           m := readMat(x#1,R);
           i := x#0;
           if H#?i then H#i = append(H#i,m)
           else H#i = {m}));
     H.WildType = wtmats;
     new TimeSeriesData from H
)

---------------------------------------------------------------------------------------------------
-- Given time series data and an integer i, functionData returns the FunctionData hashtable for function i,
-- that is the input-output (vector-scalar) data pairs corresponding to node i, if consistent; 
-- else it returns an ErrorPacket.

functionData = method(TypicalValue => FunctionData)
functionData(TimeSeriesData, ZZ) := (tsdata,v) -> (
     H := new MutableHashTable;

     -- first make the list of matrices
     mats := tsdata.WildType;
     scan(keys tsdata, x -> if class x === ZZ and x =!= v then mats = join(mats,tsdata#x));

     -- now make the hash table
     for m in mats do (
           e := entries m;
           for j from 0 to #e-2 do (
            tj := e#j;
            val := e#(j+1)#(v-1);
            if H#?tj and H#tj != val then
              return errorPacket ("in functionData: function inconsistent: point " | 
                   toString tj| " has images "|toString H#tj|
                   " and "|toString val);           
            H#tj = val;
            ));
     new FunctionData from H
)

---------------------------------------------------------------------------------------------------
-- Given function data (data for a function) and a list L of integers between 1 and n(=dim pds), 
-- corresponding to a subset of the set of variables, 
-- subFunctionData returns the function data projected to the variables in L, if consistent; 
-- else it returns an ErrorPacket

subFunctionData = method(TypicalValue => FunctionData)
subFunctionData(FunctionData, List) := (fcndata,L) -> (
     H := new MutableHashTable;
     L = apply(L, j -> j-1);
     for p in keys fcndata do (
           q := p_L;
           val := fcndata#p;
           if H#?q and H#q != val
           then return errorPacket ("in subFunctionData: function inconsistent: point " | 
            toString q| " has images "|toString H#q|
            " and "|toString val);
           H#q = val;
           );
     new FunctionData from H
)

---------------------------------------------------------------------------------------------------
-- Internal to getdiffs
-- Given 2 lists of points in k^n and a polynomial ring, getdiffs1 returns a monomial

getdiffs1 = method(TypicalValue => RingElement)
getdiffs1(List, List, Ring) := (p,q,R) -> ( 
     m := 1_R;
     scan(#p, i -> if p#i =!= q#i then m = m*R_i);
     m)

---------------------------------------------------------------------------------------------------
-- Internal to minRep; uses getdiffs1
-- Given 2 lists of lists of points in k^n, getdiffs returns a monomial ideal

getdiffs = method(TypicalValue => MonomialIdeal)
getdiffs(List, List, Ring) := (P,Q,R) -> ( 
     L := flatten apply(P, p -> apply(Q, q -> getdiffs1(p,q,R)));
     monomialIdeal L)

---------------------------------------------------------------------------------------------------
-- Previously called "sparseSets"

-- Given function data D for f_i, and a polynomial ring, minRep returns a monomial ideal.
-- Purpose of ideal: set of variables, one from each gen of the ideal, is the smallest #vars 
-- required for a consistent function; that is, the sets of vars needed for a minimal representation 
-- of the polynomial function defined by D.
-- If ideal is gen by m monomials, then sets have at most m elements

minRep = method(TypicalValue => MonomialIdeal)
minRep(FunctionData, Ring) := (fcndata,R) -> (
     Ps := apply(unique values fcndata, j -> select(keys fcndata, k -> fcndata#k === j));

     -- the next 2 commented lines were used for testing purposes
	-- print apply(Ps, a-> #a);
	-- time Ls := apply(subsets(Ps,2), x -> getdiffs(x#0,x#1,R));

     --the last 2 lines were replaced with
     print apply(Ps, a-> #a);
     Ls := apply(subsets(Ps,2), x -> getdiffs(x#0,x#1,R));

     sum Ls
)

---------------------------------------------------------------------------------------------------
-- This function doesn't always work. ???

-- Uses subFunctionData
-- Given function data D for f_i and a list L of variables xi, i=1..n, (returned from minRep)
-- findFunction computes a polynomial in the vars in L that fit D.

findFunction = method(TypicalValue => RingElement, Options => {MonomialOrder=>null})
findFunction(FunctionData, List) := o -> (fcndata,L) -> (

-- need to let user specify a term order. may have to remove "monoid"
-- if L=={}, then perhaps default should be the whole ring;
-- in this case, perhaps "findFunction" should be redefined to accept only one input (FunctionData) 
-- need to check if the order of variables given matters.

     if #L === 0 then error "expected positive number of variables";
     R := ring L#0;
     Lindices := apply(L, x -> index x + 1);
     F := subFunctionData(fcndata,Lindices);
     if instance(F, ErrorPacket) then 
         F
     else (
         S := (coefficientRing R)(monoid [L]);
         pts := transpose matrix keys F;
         vals := transpose matrix {values F};
         (A,stds) := pointsMat(pts,S);
         f := ((transpose stds) * (vals // A))_(0,0);
         substitute(f,R)
         )
)

---------------------------------------------------------------------------------------------------
-- Given function data D for f_i and a polynomial g, check evaluates g on D and 
-- returns true if g fits D and false otherwise; in this case, it returns an error statement.
-- Used to check the results of findFunction

checkFunction = method(TypicalValue => Boolean)
checkFunction(FunctionData, RingElement) := (fcndata,f) -> (
     pts := transpose matrix keys fcndata;
     Fs := makeRingMaps(pts,ring f);
     k := keys fcndata;
     s := select(0..#k-1, i -> Fs#i(f) != fcndata#(k#i));
     sp := apply(s, i -> k#i);
     if #s === 0 then true
     else (print ("function FAILS on points "|toString sp); false)
)

     
---------------------------------------------------------------------------------------------------
--+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++--
---------------------------------------------------------------------------------------------------

beginDocumentation()

document { Key => PolynomialDynamicalSystems,
     Headline => "Utilities for polynomial dynamical systems",
     EM "PolynomialDynamicalSystems", " is a package for the algebraic 
     manipulation of polynomial dynamical systems.",
     PARA{
     "The following example describes the basic usage of this package."},
     PARA{
     "In this example, the file 'wt1.dat' contains 7 time series data points for 5 nodes.
     The format of this file is: each row contains the (integer) data levels for a single node,
     separated by white space (spaces, tabs, but all on the same line).  Each row should contain 
     the same number of data points.  The knockout files have the same format.  The only difference
     is that knockout's for the i th node won't be used to determine functions for that node."},
     PARA{
     "First, we read the time series and knockout data using ", TO readTSData, ".  This produces
     a TimeSeriesData object, which is just a Macaulay2 hash table."},
     EXAMPLE {
	  ///T = readTSData({"wt1.dat"}, {(1,"ko1.dat")}, ZZ/5)///,
	  },
     "Suppose we wish to understand which nodes might affect node 2.  First, we determine
     what any such function must satisy.",
     EXAMPLE {
	  "fT = functionData(T,2)"
	  },
     "In this example, there are only seven constaints on the function.  Consequently, there are
     many functions which will satisfy these constraints.",
     PARA{
     "Next, we create a monomial ideal which encodes all of the possible sparsity patterns
     of all such functions satisfying these constraints."},
     EXAMPLE {
	  "R = ZZ/5[makeVars 7];",
	  "I = minRep(fT,R)",
	  },
     "The monomial ideal I has the property that there is a function involving 
     variables x_i1, ..., x_ir if and only if I is contained in the ideal (x_i1, ..., x_ir).
     For example, each generator of I is divisible by either x2 or x4, so there is a function 
     involving just x2 and x4 which satisfies the data.",
     PARA{
     "In order to find all minimal such sets, we use the Macaulay2 built-in function "},
     TO minimalPrimes, ".  Each monomial generator of the result encodes a minimal set.",
     EXAMPLE {
	  "minimalPrimes I"
	  },
     "The first generator tells us that there is a function involving only x2 and x4.",
     EXAMPLE {
	  "findFunction(fT,{x2,x4})"
	  },
     "The second generator tells us that there is a function involving only x3 and x4.",
     EXAMPLE {
	  "findFunction(fT,{x3,x4})"
	  }
}

document {
	Key => (checkFunction, FunctionData, RingElement),
	Headline => "given function data D and a polynomial g, evaluates g on D and returns true if g fits D and false otherwise"
}


document {
	Key => (findFunction, FunctionData, List),
	Headline => "given function data D and a list L of variables xi, i=1..n, computes a polynomial in the variables in L that fit D"
}

document {
	Key => (functionData,TimeSeriesData, ZZ),
	Headline => "given time series data and an integer i, returns a hashtable of type FunctionData for function i, that is the input-output (vector-scalar) data pairs corresponding to node i, if consistent; else returns an ErrorPacket"
}

document {
	Key => (getVars, RingElement),
	Headline => "returns the variables in a given polynomial"
}

document {
	Key => (makeVars, ZZ),
	Headline => "given an integer n, returns a list of variables {x1..xn}"
}

document {
	Key => (minRep, FunctionData, Ring),
	Headline => "given function data D and a polynomial ring, returns a monomial ideal, where the set of variables, one from each generator of the ideal, is the smallest # variables required for a consistent function; that is, the sets of variables needed for a minimal representation of the polynomial function defined by D; to be used with primaryDecomposition"
}

document { 
     Key => {readTSData, (readTSData,List,List,Ring)},
     Headline => "read time series data from a set of wild and knockout files",
     Usage => "readTSData(WT,KO,kk)",
     Inputs => {
	  "WT" => " a list of file names, containing wild type data",
	  "KO" => {" a list (i, L), where i is the variable being knocked out, and
	        L is a list of file names containing knock out data for variable i."},
	  "kk" => "the coefficient ring (usually a finite field)"
	  },
     Outputs => {
	  TimeSeriesData => "a hash table"
	  },
     Caveat => {},
     SeeAlso => {}
     }

document {
	Key => (subFunctionData,FunctionData, List),
	Headline => "given function data and a list L of integers between 1 and n(=dim pds), corresponding to a subset of the set of variables, returns the function data projected to the variables in L, if consistent; else it returns an ErrorPacket"
}

--       TimeSeriesData, 
--       FunctionData, 

end
restart
loadPackage("PolynomialDynamicalSystems", FileName=>"./ReverseEngineering/PolynomialDynamicalSystems.m2")
--installPackage("PolynomialDynamicalSystems", FileName=>"./ReverseEngineering/PolynomialDynamicalSystems.m2")
p = 5;
n = 5;
kk = ZZ/p;
R = kk[makeVars n];
T = readTSData({"./ReverseEngineering/Gepasi_WT1.st"},{(5, "./ReverseEngineering/Gepasi_ko5.st")},kk)
FD = apply(n, i->functionData(T,i+1));
Fs = apply(n, i -> findFunction(FD_i,gens R))
netList Fs

restart
loadPackage("PolynomialDynamicalSystems", FileName=>"./ReverseEngineering/PolynomialDynamicalSystems.m2")
PDS = findPDS get "./ReverseEngineering/Gepasi.json"
netList oo
toHashTable createRevEngJSONOutputModel PDS
prettyPrintJSON oo
toHashTable oo

