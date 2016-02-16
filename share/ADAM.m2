-- Code to help deal with packing and unpacking JSON for the main routines

adamRoot = getenv("ADAM_ROOT")
path = prepend(adamRoot | "/superADAM/share/", path)
needsPackage "ADAMModel"
needsPackage "JSON"

-- Create an ADAM "task" json file, from inputs
toTask = method()
toTask(Array, Array, Array) := (inputs, arguments, names) -> (
    prettyPrintJSON new HashTable from {
        "task" => new HashTable from {
            "type" => names#0,
            "method" => new HashTable from {
                "id" => names#1,
                "description" => names#2,
                "arguments" => names#3
                },
            "input" => inputs
            }
        }
    )

-- wrapped function
wrFindLimitCycles = method()
wrFindLimitCycles String := (jsonTask) -> (
    T := parseJSON jsonTask;
    M = modelFromJSONHashTable T#"task"#"input"#0;
    args = T#"task"#"method"#"arguments";
    if #args != 1 or args#0#"name" != "cycleLengths" then (
        stderr << "expected one argument named 'cycleLengths'" << endl;
        exit(1);
        );
    cycleLengths = args#0#"value";
    if not all(cycleLengths, x -> instance(x, ZZ) and x >= 1) then (
        stderr << "expected the limit cycle lengths to be positive integers" << endl;
        exit(2);
        );
    resultLimitCycles = findLimitCycles(M,{},cycleLengths);
    toJSON toHashTable {"output" => {"limitcycles" => resultLimitCycles}}
    )
end

restart
path = prepend((getenv "ADAM_ROOT")|"superADAM/share", path)
load "ADAM.m2"
dir = "~/src/reinhard/ADAM/superADAM/REACT/"
str = get (dir|"doc/sample-input.json")
H = parseJSON str
print prettyPrintJSON H

H = parseJSON get "~/src/reinhard/cell-collective-json/Apoptosis_Network.json"
("foo.json" << 
  toTask(
      [H],
      [], 
      ["blah", "limitcycles", "yada yada", [new HashTable from {"name" => "cycleLengths", "value" => [1]}]]
      )
  << endl << close
  )

