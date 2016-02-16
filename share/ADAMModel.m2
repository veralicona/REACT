
--TODO today: (9/9/14)
-- DONE --  1. add parameter values to limitCycles code
--  2. allow specialization of a model with parameters?
--DONE --  3. make sure "variables", "parameters" are lists, in the right order.
--  4. work on checkModel: it should handle more things, including parameters.  And checking updateRules...
--  5. polynomials: should call "addPolynomials" if needed?  NO...?
--  6. speed up JSON input for the two large files?
--  7. for going from TT to polys, do we need to add in ki^p-ki = 0?  Probably...


newPackage(
    "ADAMModel",
    Version => "0.1", 
    Date => "",
    Authors => {{Name => "Franziska Hinkelmann", 
            Email => "", 
            HomePage => ""},
        {Name => "Mike Stillman", 
            Email => "", 
            HomePage => ""}
        },
    Headline => "ADAM Model management",
    PackageExports => {"solvebyGB", "JSON", "LogicalFormulas"},
    DebuggingMode => true
    )

export {
    "Model", 
    "model",
    "modelFromJSONHashTable",
    "verifyModel",
    "checkModel",
    "parseModel", 
    "edges",
    "wiringDiagram",
    "polynomials", 
    "findLimitCycles", 
    "polyFromTransitionTable",
    "transformModel",
    "toMutable",
    "toImmutableModel"
    }

Model = new Type of HashTable

model = method(Options => {
        "parameters" => {},
        "updateRules" => null
        })
model List := opts -> (varlist) -> (
    parts := {
        {"variables", varlist},
        {"parameters", opts#"parameters"},
        {"updateRules", opts#"updateRules"},
        symbol cache => new CacheTable
        };
    parts = select(parts, x -> x#1 =!= null);
    model := new Model from parts;
    checkModel model;
    model.cache.ring = ring model;
    model
    )
parameters = method()
parameters Model := (M) -> (
    -- returns a list of strings
    M#"parameters"/(x -> x#"id")//toList
    )
vars Model := (M) -> (
    -- returns a list of strings
    M#"variables"/(x -> x#"id")//toList
    )
char Model := (M) -> (
     p := M#"variables"/(x -> #x#"states")//max;
     while not isPrime p do p = p+1;
     p
    )
ring Model := (M) -> (
    if not M.cache.?ring then M.cache.ring = (
        paramnames := parameters M;
        varnames := vars M;
        p := char M;
        kk := if #paramnames == 0 then ZZ/p else ZZ/p[paramnames];
        R1 := kk[varnames];
        I1 := ideal for x in gens R1 list x^p-x;
        R1/I1);
    M.cache.ring
    )

edges = method()
edges Model := (M) -> (
    flatten for x in M#"updateRules" list for j in x#"functions"#0#"inputVariables" list {j, x#"target"}
    )

--- ZZZZ
wiringDiagram = method()
wiringDiagram Model := (M) -> (
    -- output is a list of hashtables, one for each node.
    -- each hashtable contains the input edges to a node and the weights and signs (which are likely "")
    for node in M#"updateRules" list (
        hashTable {
            "target" => node#"target",
            "sources" => for v in node#"functions"#0#"inputVariables" list 
              hashTable {
                  "source" => v
                  -- also has optional fields: "weight" (value: float), "sign" (value is one of "+", "-", "") 
                  }
            }
        )
    )

-- The following is used for testing purposes
ErrorPacket == Model := (M,N) -> false
Model == ErrorPacket := (M,N) -> false
ErrorPacket == ErrorPacket := (M,N) -> checkEqual(M,N)
Model == Model := (M,N) -> checkEqual(M,N)

-- whereNotEqual: gives error, with first place where they differ
whereNotEqual = method()
whereNotEqual(String,String) := (s,t) -> 
    if s != t then error("strings: "|s|" and "|t|" differ")
whereNotEqual(List,List) := (L1,L2) -> (
    if #L1 != #L2 then error("lists: "|toString L1|" and "|toString L2| " differ in length");
    for i from 0 to #L1 - 1 do (
        whereNotEqual(L1#i, L2#i);
        );
    )
whereNotEqual(HashTable,HashTable) := (H1,H2) -> (
    k1 := sort delete(symbol cache, keys H1);
    k2 := sort delete(symbol cache, keys H2);
    if k1 =!= k2 then error("keys: "|toString k1|" and "|toString k2| " differ");
    for k in k1 do (
        whereNotEqual(H1#k, H2#k);
        );
    )
whereNotEqual(Thing,Thing) := (a,b) -> if a =!= b then error("differ: \n  "|toString a|"\n  "|toString b);
    
checkEqual = method()
checkEqual(String,String) := (s,t) -> s == t
checkEqual(List,List) := (L1,L2) -> (
    if #L1 != #L2 then return false;
    for i from 0 to #L1 - 1 do (
        if not checkEqual(L1#i, L2#i) then return false;
        );
    true
    )
checkEqual(HashTable,HashTable) := (H1,H2) -> (
    k1 := sort delete(symbol cache, keys H1);
    k2 := sort delete(symbol cache, keys H2);
    if k1 =!= k2 then return false;
    for k in k1 do (
        if not checkEqual(H1#k, H2#k) then return false;
        );
    true
    )
checkEqual(Thing,Thing) := (a,b) -> a === b


checkModel = method()
checkModel Model := (M) -> (
    -- a 'model' should have been constructed via the 'model' function.
    -- First, we check that all the keys are expected
    -- Second, we check the types of the easy ones
    -- Third, we check the structure of variables, parameters
    -- Fourth, check the updateRules
    result := M#?"variables";
    if not result then return false;
    vars := M#"variables";
    for f in vars do (
        if not f#?"id" or not instance(f#"id", String) then return false;
        if not f#?"states" or not instance(f#"states", List) then return false;
        );
    if not M#?"updateRules" then return false;
    -- TODO: check updateRules!! also to check:
    ---- updateRules matches the description in doc/
    result
    )

verifyModel = method()
verifyModel ErrorPacket := (M) -> M
verifyModel Model := (M) -> (
    -- result is either M or an ErrorPacket
    -- a 'model' should have been constructed via the 'model' function.
    -- First, we check that all the keys are expected
    keysM := set keys M - set {symbol cache};
    required := {"name", "description", "version", "variables", "updateRules"};
    optional := {"parameters", "simlab"};
    allkeys := join(required, optional);
    -- First: check that all keys are a subset of allkeys
    extras := keysM - set allkeys;
    if #extras > 0 then (
        -- there are fields we don't know about.  Return an error.
        -- No one should be adding new fields that we don't know about.
        return errorPacket("json model includes the following unknown key(s): "|toString toList extras);
        );
    -- Second: check that each key in 'required' occurs
    missing := set required - keysM;
    if #missing > 0 then (
        return errorPacket("model is missing the following required key(s): "|toString toList missing);
        );
    -- at this point we are assured that the required keys are present.
    -- Check the types of the easy ones
    if not instance(M#"name", String) then
      return errorPacket("verify model: name is not a String");
    if not instance(M#"description", String) then
      return errorPacket("verify model: description is not a String");
    if not instance(M#"version", String) then
      return errorPacket("verify model: version is not a String (it should not be a number)");
    vars := M#"variables";
    if not instance(vars, BasicList) then
      return errorPacket("verify model: 'variables' should be a list");
    for i from 1 to #vars do (
        thisvar := vars#(i-1);
        thisid := "x"|(toString i);
        key := set keys thisvar;
        -- keys should be among: {id, name, states}
        extra := key - set{"id", "name", "states"};
        missing := set{"id", "states"} - key;
        if #extra > 0 then
          return errorPacket("verify model: unexpected key(s) for variable: "|toString extra);
        if #missing > 0 then
          return errorPacket("verify model: missing key(s) for variable: "|toString missing);
        -- now check the value of "id", and "states"
        if not instance(thisvar#"id", String) then
          return errorPacket("verify model: id for variable should be: '"|thisid|"'");
        if thisvar#"id" != thisid then
          return errorPacket("verify model: variable id '"|(thisvar#"id")|"' is not as expected: '"|("x"|(toString i))|"'");
        if not instance(thisvar#"states", BasicList) 
           or not all(thisvar#"states", f -> instance(f, String) or instance(f,ZZ)) then
          return errorPacket("verify model: variable "|thisid|" states is not a list of strings or integers");
        );
      -- each element of 'vars' should have: ...
    updates := M#"updateRules";
    if not instance(updates, BasicList) then
      return errorPacket "verify model: updateRules must be a list";
    if #updates =!= #vars then
      return errorPacket("verify model: #updateRules is "|toString (#updates)|" should match "|toString (#vars));
    -- Fourth, check the updateRules
    ---- updateRules matches the description in doc/
    M
    )

modelFromJSONHashTable = method()
modelFromJSONHashTable HashTable := (M) -> (
    -- XXXX
    if instance(M, ErrorPacket) then return M;
    keysM := set keys M;
    required := {"type", "updateRules", "numberVariables", "fieldCardinality"};
    -- check that each key in 'required' occurs
    missing := set required - keysM;
    if #missing > 0 then (
        return errorPacket("model is missing the following required key(s): "|toString toList missing);
        );
    -- Note: actual types are checked in 'checkModel', not here
    if not M#"type" === "model" then 
      return errorPacket "internal error: input is not a Model or ErrorPacket";
    varlist := if M#?"variables" then M#"variables" else (
        -- create varlist from updateRules
        for i from 0 to #M#"updateRules"-1 list (
            hashTable{"id" => M#"updateRules"#i#"target", 
                "states" => for j from 0 to M#"fieldCardinality"-1 list toString j
                })
        );
    model(varlist,
        "parameters" => if M#?"parameters" then M#"parameters" else {},
        "updateRules" => M#"updateRules"
        )
    )

-- parseModel: takes a string (usually the contents of a file), and returns
-- a "Model", if everything works, or an ErrorPacket
parseModel = method()
parseModel String := (str) -> (
    M := parseJSON str;
    modelFromJSONHashTable M
    )

toJSONHashTable = method()
toJSONHashTable Model := (M) -> (
    ks := select(pairs M, x -> instance(x#0, String));
    new HashTable from prepend("type"=>"model", ks)
    )

toJSON Model := (M) -> toJSON toJSONHashTable M

prettyPrintJSON Model := (M) -> (
    prettyPrintJSON toJSONHashTable M
    )

polynomials = method()
polynomials Model := (M) -> (
    -- Returns a list of lists of polynomials.
    -- For a well-defined model, each list of polynomials has length 1.
    M = transformModel("add","poly",M);
    if instance(M, ErrorPacket) then error "cannot determine all polynomials";
    R := ring M;
    use R;
    -- first: make sure that polynomial functions are present
    -- then: returns a list of list of polynomials
    for x in M#"updateRules" list (
        for f in x#"functions" list (
            if not f#?"polynomialFunction"
            then error "internal error: polynomial not found"
            else (
                g := value f#"polynomialFunction";
                if ring g =!= R then promote(g,R) else g
                )
            )
        )
    )

polynomials(Model,List) := (M,parameterValues) -> (
    polys := polynomials M;
    R := ring M;
    kk := coefficientRing R;
    base := ring ideal kk;
    if base =!= ZZ then (
        p := char kk;
        R1' := (coefficientRing kk)(monoid R);
        I1' := ideal for x in gens R1' list x^p-x;
        R1 := R1'/I1';
        phi := map(R1, R, (generators R1) | parameterValues);
        polys = for f in polys list for g in f list phi g
        );
    polys
    )

toArray = method()
toArray List := (L) -> new Array from (L/toArray)
toArray Thing := (L) -> L

findLimitCycles = method()
findLimitCycles(Model, List, ZZ) := (M, parameterValues, limitCycleLength) -> 
    findLimitCycles(M, parameterValues, {limitCycleLength})
findLimitCycles(Model, List, List) := (M, parameterValues, limitCycleLengths) -> (
    PDS := polynomials(M, parameterValues);
    if not all(PDS, f -> length f === 1)
    then return errorPacket "expected model with only one function per node";
    mat := matrix{flatten PDS};
    H := for len in limitCycleLengths list (
        limitcycles := gbSolver(mat, len);
        len => toArray limitcycles
        );
    hashTable H
    )

polyFromTransitionTable = method()
polyFromTransitionTable(List, List, Ring) := (inputvars, transitions, R) -> (
    --<< "starting interpolation: " << #inputvars << endl;
    p := char R;
    n := #inputvars;
    X := set (0..p-1);
    inputs := sort toList X^**n;
    result := sum for t in transitions list (
        input := t#0; -- a list
        output := t#1; -- a value
        if output == 0 then continue else
        output * product for i from 0 to n-1 list (
            x := R_(inputvars#i);
            1 - (x-input#i)^(p-1)
        ));
    if result == 0 then 0_R else result -- this is just being careful...
    )

transformer = new MutableHashTable;
--transformer#("add","bool") = notImplemented

transformer#("add","poly") = (updatexi, M) -> (
    R := ring M;
    if updatexi#?"polynomialFunction" then (
        updatexi#"polynomialFunction" = toString value updatexi#"polynomialFunction";
        ) 
    else if updatexi#?"transitionTable" then (
        possibles := updatexi#"inputVariables";
        tt := updatexi#"transitionTable";
        updatexi#"polynomialFunction" = 
            toString polyFromTransitionTable(possibles, tt, R);
        )
    else if updatexi#?"booleanFunction" then (
        P := makeLFParser R;
        F := P updatexi#"booleanFunction";
        updatexi#"polynomialFunction" = toString F;
        )
    )

transformer#("add","tt") = (updatexi, M) -> (
    R := ring M;
    if updatexi#?"transitionTable" then return;
    if updatexi#?"booleanFunction" then (
        possibles := updatexi#"inputVariables";
        Q := makeBoolParser R;
        formula := Q updatexi#"booleanFunction";
        updatexi#"transitionTable" = 
            transitionTable(possibles, formula);
        )
    else if updatexi#?"polynomialFunction" then (
        possibles = updatexi#"inputVariables";
        F := value updatexi#"polynomialFunction";
        updatexi#"transitionTable" = 
            transitionTable(possibles/value, F);
        )
    )

transformer#("remove","poly") = (updatexi,M) -> remove(updatexi,"polynomialFunction")
transformer#("remove","tt") = (updatexi,M) -> remove(updatexi,"transitionTable")
transformer#("remove","bool") = (updatexi,M) -> remove(updatexi,"booleanFunction")

transformModel = method()
transformModel(String, String, ErrorPacket) := (add, type, M) -> M
transformModel(String, String, Model) := (add, type, M) -> (
    if not transformer#?(add,type) then (
        packet := "error: cannot " | add | " transition functions of type: "|type;
        return errorPacket packet
        );
    f := transformer#(add,type);
    M1 := toMutable M;
    -- At this point, we loop through and run the function
    update := M1#"updateRules";
    -- update is a list of lists of functions
    for k in update do (
        fcns := k#"functions";
        for fcn in fcns do f(fcn, M);
        );
    -- Finally, we return the new model
    toImmutableModel M1
    )

toMutable = method()
toMutable HashTable := (H) -> new MutableHashTable from (
    for k in keys H list k => toMutable H#k
    )
toMutable BasicList := (L) -> apply(L, toMutable)
toMutable CacheTable := (F) -> F
toMutable RingElement := (F) -> F
toMutable Ring := (F) -> F
toMutable String := (F) -> F
toMutable Thing := (x) -> x

toImmutable = method()
toImmutable HashTable := (H) -> new HashTable from (
    for k in keys H list k => toImmutable H#k
    )
toImmutable(HashTable,Ring) := (H,R) -> new HashTable from (
    prepend(symbol cache => new CacheTable from {symbol ring => R},
        for k in keys H list k => toImmutable H#k)
    )
toImmutable BasicList := (L) -> apply(L, toImmutable)
toImmutable CacheTable := (F) -> F
toImmutable RingElement := (F) -> F
toImmutable Ring := (F) -> F
toImmutable String := (F) -> F
toImmutable Thing := (x) -> x

toImmutableModel = method()
toImmutableModel HashTable := (H) -> new Model from toImmutable H
toImmutableModel(HashTable,Ring) := (H,R) -> new Model from
    toImmutable(H,R)

TEST ///
{*
  restart
*}
  needsPackage "ADAMModel"
  needsPackage "JSON"

  str = exampleJSON#0

  M = parseModel str
  result = findLimitCycles(M,{},{1,2,3})
  ans = new HashTable from {1 => [[[0,1,1]]], 2 => [], 3 => []}
  assert(result === ans)
///

   sample2 = ///{
  "type": "model",
  "description": "",
  "name": "Sample2 for testing",
  "version": "1.0",
  "parameters": [],
  "variables": [
      {
      "id": "x1",
      "name": "variable1",
      "states": ["0","1"]
      },
      {
      "id": "x2",
      "name": "variable2",
      "states": ["0","1"]
      },
      {
      "id": "x3",
      "name": "variable3",
      "states": ["0","1"]
      },
      {
      "id": "x4",
      "name": "variable4",
      "states": ["0","1"]
      },
      {
      "id": "x5",
      "name": "variable5",
      "states": ["0","1"]
      }
    ],
  "updateRules": [
      {
      "functions": [
          {
          "inputVariables": ["x2","x3","x1"],
          "transitionTable": [
              [[0,0,0],1],
              [[0,0,1],0],
              [[0,1,0],0],
              [[0,1,1],0],
              [[1,0,0],1],
              [[1,0,1],1],
              [[1,1,0],0],
              [[1,1,1],0]           
            ],
           "polynomialFunction": "x1+x2+x3"
          }
        ],
      "target": "x1"
      },
      {
      "functions": [
          {
          "inputVariables": ["x1","x2"],
          "polynomialFunction": "x1+1"
          }
        ],
      "target": "x2"
      },
      {
      "functions": [
          {
          "inputVariables": ["x1","x2"],
          "polynomialFunction": "x1+x2"
          }
        ],
      "target": "x3"
      },
      {
      "functions": [
          {
          "inputVariables": ["x1","x4"],
          "polynomialFunction": "x1+x4"
          }
        ],
      "target": "x4"
      },
      {
      "functions": [
          {
          "inputVariables": ["x2","x5"],
          "polynomialFunction": "x2+x2*x5+x5"
          }
        ],
      "target": "x5"
      }
    ]
  }
///
   
TEST ///
{*
  restart
*}
  debug needsPackage "ADAMModel"
  M = parseModel sample2

  ring M
  vars M
  flatten polynomials M
 

  M1 = transformModel("add", "poly", M)
  M2 = transformModel("add", "poly", M1)
  assert(M1 == M2)
  M3 = transformModel("remove", "tt", M2)
  M4 = transformModel("add", "tt", M3)

  N1 = transformModel("remove", "poly", M4)  
  N2 = transformModel("remove", "tt", M4)  
  N3 = transformModel("add", "poly", N1)
  N4 = transformModel("add", "tt", N2)
  assert(N3 == N4)
  assert(M3 != M2)
  assert(ring N4 === ring M)
///

///
{*
  restart
*}

  debug needsPackage "ADAMModel"
  str = get "../../exampleJSON/SecondVersion1-Model.json"
  M = parseModel str
  prettyPrintJSON M
  M1 = transformModel("add","poly",M)
  prettyPrintJSON M1

  findLimitCycles(M1,{},{1,2,3})
  toJSON M1
  polynomials M1
  R = ring M
  R === ring M

///

TEST ///
  -- Test transformModel
{*
  restart
*}
  needsPackage "ADAMModel"
  needsPackage "JSON"

  str = exampleJSON#0
  M = parseModel str
  mM = toMutable M
  peek mM
  M1 = toImmutableModel mM
  mM#"updateRules"#"x1"#"polynomialFunction" = "x1+x2"
  M2 = toImmutableModel mM
  assert(M == M1)
  assert(M != M2)
  assert(M1 != M2)

  M1 = transformModel("add","poly",M)
  assert(M == M1);
  
///

TEST ///
{*
restart
*}
    debug needsPackage "ADAMModel"
    str = get (currentDirectory()|"../../exampleJSON/BooleanModels/Keratinocyte.json");
    M = parseModel str
    -- these have boolean and polys
    -- test: bool --> poly
    M1 = transformModel("remove","poly",M)
    M2 = transformModel("add","poly",M1)
    whereNotEqual(M,M2)
    assert(M == M2)

    -- test bool --> transition table
    --  matches poly --> transition table
    T1 = transformModel("add","tt",M1);
    T2 = transformModel("remove","bool",T1)

    T3 = transformModel("remove","bool",M2)
    T4 = transformModel("add","tt",T3)    
    T5 = transformModel("remove","poly",T4)

    assert(T2 == T5)

    -- test bool --> poly, and transition --> poly have same value
    -- This test is messed up MES
    S1 = transformModel("add","poly",M1) -- bool --> poly
    S2 = transformModel("remove","bool",S1) -- just tt from bool
    S3 = transformModel("add","tt",S2)
    
///
end

beginDocumentation()

doc ///
Key
  Model
Headline
Description
  Text
  Example
Caveat
SeeAlso
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///
