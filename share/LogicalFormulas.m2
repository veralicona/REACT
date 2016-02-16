-- to add to this:
--   1. correctness check: a version which creates an expression with NOT, OR, AND, and then evaluates it
--      at all points
--   2. Parser for polynomials along the same lines
--   3. If possible, the parser should not give an M2 error
--   4. Char > 2 expressions should be do-able in this manner too, once we know what we want
--
-- Create a new model from a file, with one line per function
-- 
newPackage(
        "LogicalFormulas",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "translation of logical formulas to polynomials",
        DebuggingMode => true
        )

needsPackage "Parsing"
debug Core

export {
    "makeLFParser",
    "makeBoolParser",
    "ErrorString",
    "logicEvaluate",
    "LogicalAnd",
    "LogicalOr",
    "LogicalNot",
    "logicalOr",
    "logicalAnd",
    "logicalNot",
    "transitionTable",
    "possibleInputs"
    }

--------------------------------------------------------
-- logical expressions ---------------------------------
-- support and evaluation 
-- used in makeBoolParser, transitionTable
--  and also in general assertion checking
LogicalAnd = new Type of List
LogicalOr = new Type of List
LogicalNot = new Type of List
logicalOr = a -> new LogicalOr from a
logicalAnd = a -> new LogicalAnd from a
logicalNot = a -> new LogicalNot from a

logicEvaluate = method()
logicEvaluate(String, HashTable) := (x, env) -> env#x 
logicEvaluate(String, MutableHashTable) := (x, env) -> env#x 
logicEvaluate(LogicalOr, HashTable) := (L, env) -> any(L, x -> logicEvaluate(x,env))
logicEvaluate(LogicalAnd, HashTable) := (L, env) -> all(L, x -> logicEvaluate(x,env))
logicEvaluate(LogicalNot, HashTable) := (L, env) -> not logicEvaluate(L#0, env)
logicEvaluate(Boolean, HashTable) := (L, env) -> L


support String := s -> {s}
support LogicalNot :=
support LogicalOr := 
support LogicalAnd := (L) -> sort toList sum for x in L list set support x

----------------------------------------------------------------
-- The parser should return either a value, or an ErrorString --
----------------------------------------------------------------
ErrorString = new Type of List -- list of 1 element: a string
errorString = method()
errorString String := (s) -> new ErrorString from {s}


---------------------------------------------------------
-- Some code which perhaps should be in Parser.m2 -------
---------------------------------------------------------
alphanum = set characters "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
alphanumParser = Parser (c -> if alphanum#?c then new Parser from (b -> if b === null then c))

digits = set characters "0123456789"    
digitParser = Parser (c -> if digits#?c then new Parser from (b -> if b === null then c))

idenParser = (env) -> (
    a -> (
        v := concatenate a; 
        if env#?v then env#v else errorString("parse error: unknown variable '"|v|"'")
        )
    ) % letterParser @ (+alphanumParser)
binOp = (op, parser, fcn) -> fcn % parser @ +(last % op @ parser)
unOp = (op, parser, fcn) -> fcn % op @ parser

----------------------------------------------------------
-- Parser for Logical Models #1: parses to a polynomial --
-- usage: P = makeLFParser R
--        P "x3 | (x4&(x5|!x6)&x2) | (x2&x3)"
----------------------------------------------------------
makeEnvironment = method()
makeEnvironment Ring := (R) -> (
    V := gens(R, CoefficientRing => ZZ);
    hashTable for v in V list (toString v) => v
    )

fcnNot = a -> if class a#1 === ErrorString then a#1 else 1-a#1
fcnOr = a -> (
    a1 := deepSplice a; 
    if any(a, x -> instance(x,ErrorString)) then (
        strs := select(1, a1, x -> instance(x,ErrorString));
        strs#0
        )
    else 1 - times apply(a1, x -> 1-x)
    )
fcnAnd = a -> (
    a1 := deepSplice a; 
    if any(a, x -> instance(x,ErrorString)) then (
        strs := select(1, a1, x -> instance(x,ErrorString));
        strs#0
        )
    else times a1
    )

makeLFParser = method()
makeLFParser Ring := (R) -> (
    env := makeEnvironment R; -- all variables of R, and of coefficient rings of R
    idenP := idenParser env;
    exprP1:= null;
    exprP := futureParser symbol exprP1;
    parenP := (a -> a#1#0) % ("(" @ exprP @ ")");
    expr2 := ((a -> a_R) % NNParser) 
      | idenP 
      | parenP 
      | unOp("!", idenP, fcnNot) 
      | unOp("!", parenP, fcnNot);
    exprP1 = expr2 | binOp("|", expr2, fcnOr) | binOp("&", expr2, fcnAnd);
    exprP1 : nonspaceAnalyzer
    )

----------------------------------------------------------
-- Parser for Logical Models #2: parses to a logical expression
-- usage: Q = makeBoolParser R
--        Q "x3 | (x4&(x5|!x6)&x2) | (x2&x3)"
----------------------------------------------------------
makeStringEnvironment = method()
makeStringEnvironment Ring := (R) -> (
    V := gens(R, CoefficientRing => ZZ);
    hashTable for v in V list (toString v) => (toString v)
    )

boolNot = a -> if class a#1 === ErrorString then a#1 else logicalNot {a#1}
boolOr = a -> (
    a1 := deepSplice a; 
    if any(a, x -> instance(x,ErrorString)) then (
        strs := select(1, a1, x -> instance(x,ErrorString));
        strs#0
        )
    else logicalOr toList a1
    )
boolAnd = a -> (
    a1 := deepSplice a; 
    if any(a, x -> instance(x,ErrorString)) then (
        strs := select(1, a1, x -> instance(x,ErrorString));
        strs#0
        )
    else logicalAnd toList a1
    )

makeBoolParser = method()
makeBoolParser Ring := (R) -> (
    env := makeStringEnvironment R; -- all variables of R, and of coefficient rings of R
    idenP := idenParser env;
    exprP1:= null;
    exprP := futureParser symbol exprP1;
    parenP := (a -> a#1#0) % ("(" @ exprP @ ")");
    expr2 := ((a -> a == 1) % NNParser) 
      | idenP 
      | parenP 
      | unOp("!", idenP, boolNot) 
      | unOp("!", parenP, boolNot);
    exprP1 = expr2 | binOp("|", expr2, boolOr) | binOp("&", expr2, boolAnd);
    exprP1 : nonspaceAnalyzer
    )

--------------------------------------------------------
-- creating transition tables --------------------------
--------------------------------------------------------
possibleInputs = method()
possibleInputs(ZZ,ZZ,ZZ) := (ninputs, loval, hival) -> (
    f := n -> (
        if n == 0 then {{}}
        else (
            prev := f (n-1);
            flatten for i from loval to hival list 
              for x in prev list prepend(i,x)
            ));
    f ninputs
    )

transitionTable = method()
transitionTable(List, ZZ) := (inputVariables, val) -> (
    -- this is the case of a constant function, if inputVariables is empty
    if #inputVariables == 0 then {{{},val}}
    else (
        R := ring first inputVariables;
        assert all(inputVariables, x -> ring x === R);
        transitionTable(inputVariables, val_R)
        )
    )
transitionTable(List, RingElement) := (inputVariables, F) -> (
    if #inputVariables == 0 then (
        assert(support F === {});
        {{{},F}}
        )
    else (
        R := ring F;
        kk := coefficientRing ring F;
        ninputs := #inputVariables;
        inputs := possibleInputs(ninputs, 0, char kk - 1);
        locs := inputVariables/index;
        pt := new MutableList from for i from 0 to numgens R - 1 list 0_kk;
        for inp in inputs list (
            subs := for v from 0 to ninputs-1 do pt#(locs#v) = inp#v;
            sub1 := new List from pt;
            phi := map(kk,R,matrix(kk,{sub1}));
            val := lift(phi F,ZZ);
            if val < 0 then val = val + char kk;
            {inp, val}
            )
        )
    )
transitionTable(List, LogicalAnd) := 
transitionTable(List, LogicalOr) := 
transitionTable(List, LogicalNot) := 
transitionTable(List, Boolean) := 
transitionTable(List, String) := (inputVariables, F) -> (
    -- now F is a boolean formula
    -- step 1: create the possible input values (of 0, 1 values)
    -- ASSUMPTION: inputVariables is a list of strings containing all the vars occuring in F
    varlist := for v in inputVariables list if instance(v,String) then v else toString v ;
    nslots := #varlist;
    inputs := possibleInputs(nslots, 0, 1);
    env := new MutableHashTable;
    for inp in inputs list (
        for i from 0 to nslots-1 do env#(varlist#i) = (inp#i == 1);
        val := logicEvaluate(F, env);
        {inp, if val then 1 else 0}
        )
    )

beginDocumentation()

TEST ///
{*
  restart
  debug needsPackage "LogicalFormulas"
*}

  A = ZZ/2[x1,x2,x3,x4,x5,x6,x7,x8,x9,x10]
  R = A/(ideal for x in gens A list x^2-x)
  P = makeLFParser R
  Q = makeBoolParser R  

  str = "x1|x3|(x4&!x9)";
  F1 = P str
  inputvars := support F1
  tran1 = transitionTable(inputvars,F1)
  F2 = Q str
  tran2 = transitionTable(inputvars,F2)
  assert(tran1 == tran2)
///

TEST ///
{*
  restart
*}

  debug needsPackage "LogicalFormulas"

  A = ZZ/2[x1,x2,x3,x4]
  R = A/(ideal for x in gens A list x^2+x)
  env = makeEnvironment R
  P = makeLFParser R

  assert(P "1" == 1_R)
  assert(P "x3|1" == 1_R)
  assert(P "x3|0" == x3)
  assert(P "x3" == x3)
  assert(P "x3&1" == x3)
  assert(P "x3&0" == 0)
  assert(P "x1" == x1)
  assert(P "! x1" == 1+x1)
  assert(instance(P "!x5",ErrorString))
  assert(P "(!x3)" == x3+1)
  assert(P "(x4)" == x4)
  assert(P "!(x2)" == x2+1)
  assert(P "!(!x2)" == x2)
  assert(P "(x1|(x2|x1)|!x3)" == 1 + (1+x1)*(1+x2)*x3)
  assert(P "(x1|(x2&!x1)|!x3)" == 1 + (x1+1)*(1 + x2*(1+x1))*x3)
  assert(P "(x1&x2&x3&!x4)" == x1*x2*x3*(1+x4))
  assert(P "x1|x1" == x1)
///

TEST ///
  needsPackage "LogicalFormulas"

  A = ZZ/2[x1,x2,x3,x4]
  R = A/(ideal for x in gens A list x^2+x)
  P = makeBoolParser R

  assert(P "1" == true)
  assert(P "0" == false)
  assert(P "x3|1" == logicalOr{"x3",true})
  assert(P "x3|0" == logicalOr{"x3", false})
  assert(P "x3" == "x3")
  assert(P "x3&1" == logicalAnd{"x3",true})
  assert(P "x3&0" == logicalAnd{"x3",false})
  assert(P "x1" == "x1")
  assert(P "! x1" == logicalNot{"x1"})
  assert(instance(P "!x5",ErrorString))
  assert(P "(!x3)" == logicalNot{"x3"})
  assert(P "(x4)" == "x4")
  assert(P "!(x2)" == logicalNot{"x2"})
  assert(P "!(!x2)" == logicalNot{logicalNot{"x2"}})
  assert(P "(x1|(x2|x1)|!x3)" == logicalOr{"x1", logicalOr{"x2","x1"}, logicalNot{"x3"}})
  assert(P "(x1|(x2&!x1)|!x3)" == logicalOr{"x1", logicalAnd{"x2",logicalNot{"x1"}}, logicalNot{"x3"}})
  assert(P "(x1&x2&x3&!x4)" == logicalAnd{"x1","x2","x3",logicalNot{"x4"}})
  assert(P "x1|x1" == logicalOr{"x1","x1"})
///

TEST ///
  makeBooleanRing = (n) -> (
      A := ZZ/2[for i from 1 to n list ("x"|toString i)];
      I := for x in gens A list x^2+x;
      B := A/I;
      B
      );
  R = makeBooleanRing 104
  str = "(x79 & x84 & x97 &  !(x75 & x92)) | (x80 & x84 & x97 &  !(x75 & x92)) | (x96 & x84 & x97 &  !(x75 & x92)) | (x102 & x84 & x97 &  !(x75 & x92)) | (x87 & x84 & x97 &  !(x75 & x92)) | (x89 & x69 & x97 &  !(x75 & x92)) | (x90 & x84 & x97 &  !(x75 & x92)) | (x93 & x84 & x97 &  !(x75 & x92))"
  P = makeLFParser R
  Q = makeBoolParser R
  F1 = P str;
  F2 = Q str;
  assert(F1//support/toString//sort == F2//support//sort)
  possibles = support F1
  time tran1 = transitionTable(possibles, F1);
  time tran2 = transitionTable(possibles, F2);
  assert(tran1 == tran2)
///



end

doc ///
Key
  LogicalFormulas
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


