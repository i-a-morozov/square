(* Square Matrix Method *)
(* 10.1103/PhysRevAccelBeams.20.034001 *)
(* I.M. 2024 *)

(* ################################################################################################################## *)
(* SET GLOBAL PARAMETERS *)
(* ################################################################################################################## *)

ClearAll[sm$set$global] ;

sm$set$global::usage = "sm$set$global[dimension,degree,chop,accuracy] -- set global parameters for given phase space dimension <dimension>, computation degree <degree>, chop <chop> and accuracy <accuracy> " ;

sm$set$global[                                    (* -- set global parameters *)
    dimension_,                                   (* -- phase space dimension *)
    degree_,                                      (* -- total monomial degree *)
    chop_:10.0^-12,                               (* -- chop delta *)
    accuracy_:$MachinePrecision                   (* -- accuracy *)
] := Block[
    {},
    sm$dimension = dimension ;
    sm$degree = degree ;
    sm$exponents = (Reverse[FrobeniusSolve[ConstantArray[1, sm$dimension], #]] &) /@ Range[sm$degree] ;
    sm$counts = Length /@ sm$exponents ;
    sm$intervals = Transpose[{Most[Accumulate[Join[{1}, sm$counts]]], Accumulate[sm$counts]}] ;
    sm$size = Total[sm$counts] ;
    sm$table = IdentityMatrix[sm$dimension] ;
    sm$table = (First[DeleteCases[First[Outer[{#2, #1 - #2} & , {#1}, sm$table, 1]], {_, {___, -1, ___}}]] & ) /@ Flatten[sm$exponents, 1] ;
    sm$table = sm$table /. Dispatch[Thread[Flatten[sm$exponents, 1] -> Range[sm$size]]] ;
    sm$table = DeleteCases[sm$table, {(0)..}, Infinity] ;
    sm$monomials = ToExpression[Array[StringTemplate["z$`1`"], sm$dimension]] ;
    sm$monomials = Function @@ {sm$monomials, (Times @@ (sm$monomials^#) & ) /@ Flatten[sm$exponents, 1]} ;
    sm$delta = chop ;
    sm$chop = Activate[Inactivate[Chop[#, sm$delta] &]] ;
    sm$accuracy = Activate[Inactivate[SetAccuracy[#, accuracy] &]] ;
] ;

ClearAll[sm$dimension] ;
ClearAll[sm$degree]    ;
ClearAll[sm$exponents] ;
ClearAll[sm$counts]    ;
ClearAll[sm$intervals] ;
ClearAll[sm$size]      ;
ClearAll[sm$table]     ;
ClearAll[sm$monomials] ;
ClearAll[sm$delta]     ;
ClearAll[sm$chop]      ;
ClearAll[sm$accuracy]  ;

(* ################################################################################################################## *)
(* MAKE MAP *)
(* ################################################################################################################## *)

ClearAll[sm$make$map] ;

sm$make$map::usage = "sm$make$map[mat,map] -- make map for given Floquet transformation matrix <matrix> and original system mapping <mapping> " ;

sm$make$map[                                      (* -- make map in eigenmonomial basis (Q - I*P, Q + I*P) *)
    matrix_,                                      (* -- Floquet transformation matrix *)
    mapping_                                      (* -- map to transform *)
] := Block[
    {sm$variables, sm$transformation, sm$forward, sm$inverse, sm$output},
    sm$variables = ToExpression[Array[StringTemplate["z$`1`"], sm$dimension]] ;
    sm$transformation = Fold[ArrayFlatten[{{#1, 0}, {0, #2}}] & , ConstantArray[Inverse[{{1, -I}, {1, I}}], sm$dimension/2]] ;
    sm$direct = Simplify[matrix . sm$transformation] ;
    sm$inverse = Simplify[Inverse[sm$direct]] ;
    sm$output = sm$inverse . mapping[sm$direct . sm$variables] ;
    sm$output = Function @@ {sm$variables, sm$chop[PowerExpand @* Expand @* TrigToExp /@ sm$output]} ;
    sm$forward = Function @@ {sm$variables, Thread[sm$variables -> sm$direct . sm$variables]} ;
    sm$inverse = Function @@ {sm$variables, Thread[sm$variables -> sm$inverse . sm$variables]} ;
    {{sm$forward, sm$inverse}, sm$output}
] ;


(* ################################################################################################################## *)
(* MAKE JET REPRESENTATION FOR GIVEN OBSERVABLE MULTIARGUMENT FUNCTION *)
(* ################################################################################################################## *)

ClearAll[sm$make$jet] ;

sm$make$jet::usage = "sm$make$jet[observable] -- make jet  for given observable (multivariable function) <observable> " ;

sm$make$jet[                                      (* -- make jet representation for given observable *)
    observable_                                   (* -- observable multivariable function *)
] := Block[
    {sm$variables, sm$monomial, sm$rule},
    sm$variables = ToExpression[StringTemplate["z$`1`"] /@ Range[sm$dimension]] ;
    sm$monomial /: sm$monomial[x__] * sm$monomial[y__] := sm$monomial @@ ({x} + {y}) ;
    sm$monomial /: sm$monomial[x__]^(y_) := sm$monomial @@ ({x}*y) ;
    sm$rule = Thread[Rule @@ Transpose[Thread[{sm$variables, (Apply[sm$monomial]) /@ IdentityMatrix[sm$dimension]}]]] ;
    D[observable @@ sm$variables /. sm$rule, {sm$monomials @@ sm$variables /. sm$rule}]
] ;

(* ################################################################################################################## *)
(* MAKE OBSERVABLE REPRESENTATION FOR GIVEN JET *)
(* ################################################################################################################## *)

ClearAll[sm$make$observable] ;

sm$make$observable::usage = "sm$make$observable[jet] -- make observable for given jet representation <jet> " ;

sm$make$observable[                               (* -- make observable for given jet representation *)
    jet_                                          (* -- jet *)
] := Block[
    {sm$variables},
    sm$variables = ToExpression[StringTemplate["z$`1`"] /@ Range[sm$dimension]] ;
    Function @@ {sm$variables, jet . sm$monomials @@ sm$variables}
] ;

(* ################################################################################################################## *)
(* JET MULTIPLICATION  *)
(* ################################################################################################################## *)

ClearAll[sm$make$mult] ;

sm$make$mult::usage = "sm$make$mult[] -- make jet multiplication functions (sm$mult and sm$mult$compiled) " ;

sm$make$mult[                                     (* -- make jet multiplication function *)

] := Block[
    {sm$epsilon, sm$variables, sm$probe, sm$other, sm$argument, sm$product},
    sm$epsilon /: sm$epsilon^(sm$power_) /; sm$power > sm$degree = 0 ;
    sm$variables = ToExpression[StringTemplate["z$`1`"] /@ Range[sm$dimension]] ;
    sm$probe = ToExpression[Array[StringTemplate["x`1`"], sm$size]] ;
    sm$other = ToExpression[Array[StringTemplate["y`1`"], sm$size]] ;
    sm$argument = Join[sm$probe, sm$other]; sm$probe = Collect[sm$make$observable[sm$probe] @@ (sm$epsilon*sm$variables), sm$epsilon] ;
    sm$other = Collect[sm$make$observable[sm$other] @@ (sm$epsilon*sm$variables), sm$epsilon] ;
    sm$product = Collect[sm$probe*sm$other, sm$epsilon] ;
    sm$product = CoefficientList[sm$product, sm$epsilon] ;
    sm$product = Function @@ {sm$variables, Total[ParallelMap[Expand, sm$product]]} ;
    sm$product = sm$make$jet[sm$product] ;
    sm$mult = Activate[Inactivate[Block[sm$argument, sm$argument = Flatten[#] ; sm$product] & ]] ;
    sm$mult$compiled = Compile[
        {{sm$argument, _Complex, 2}},
        sm$mult[sm$argument],
        "CompilationOptions" -> {{"InlineExternalDefinitions" -> True},
        {"ExpressionOptimization" -> True}}, "RuntimeOptions" -> "Speed",
        RuntimeAttributes -> {Listable},
        Parallelization -> True,
        CompilationTarget -> "WVM"
    ] ;
] ;

(* ################################################################################################################## *)
(* JET MULTIPLICATION (OPTIMIZE) *)
(* ################################################################################################################## *)

ClearAll[sm$optimize$mult] ;

sm$optimize$mult::usage = "sm$optimize$mult[map] -- jet multiplication optimization for given mapping <map> " ;

sm$optimize$mult[                                 (* -- jet multiplication optimization *)
    map_                                          (* -- map *)
] := Block[
    {sm$jet, sm$argument, sm$data, sm$rule, sm$local},
    sm$jet = sm$chop[sm$make$jet[map]] ;
    sm$argument = Extract[sm$mult, {1, 1}] ;
    sm$argument = Last[Partition[sm$argument, sm$size]] ;
    sm$data = sm$argument ;
    sm$data = ConstantArray[sm$data, sm$dimension] ;
    sm$data = Transpose[{sm$jet, sm$data}] ;
    sm$data = sm$chop[sm$mult /@ sm$data] ;
    sm$rule = Drop[TakeList[sm$argument, sm$counts], - (1 + 1)] ;
    sm$rule = Join[{{}}, sm$rule] ;
    sm$rule = FoldList[Join, sm$rule] ;
    sm$rule = (Dispatch[Thread[# -> 0]] & ) /@ sm$rule ;
    sm$data = Transpose[sm$chop[sm$data /. sm$rule]] ;
    sm$local = sm$degree - 1 ;
    ClearAll[sm$mult$optimized] ;
    Do[
        Do[
            Block[
                {sm$code},
                sm$code = sm$data[[i, j]] ;
                sm$code = sm$chop[Expand /@ sm$code] ;
                sm$mult$optimized[i][j + 1] = Activate[Inactivate[Block[sm$argument, sm$argument = # ; sm$code] & ]] ;
            ],
            {j, 1, sm$local}
        ],
        {i, 1, sm$dimension}
    ] ;
] ;

(* ################################################################################################################## *)
(* SQUARE MATRIX *)
(* ################################################################################################################## *)

ClearAll[sm$make$matrix] ;

sm$make$matrix::usage = "sm$make$matrix[method, mapping] -- make square matrix for given transformation <mapping> using the method <method> (\"DIRECT\",\"JET\",\"OPTIMIZED\" or \"COMPILED\")" ;

Options[sm$make$matrix] = {
    "Verbose" -> False,                           (* -- verbose flag (True/False) *)
    "Parallelize" -> False                        (* -- parallelize flag (True/False) *)
} ;

(* ################################################################################################################## *)

sm$make$matrix[                                   (* -- make square matrix *)
    "DIRECT",                                     (* -- "DIRECT" computation method *)
    map_,                                         (* -- map *)
    opt:OptionsPattern[]                          (* -- option(s) *)
] := Block[
    {sm$function, sm$print, sm$time, sm$epsilon, sm$variables, sm$monomial, sm$rules, sm$list, sm$matrix},
    sm$function = If[OptionValue["Parallelize"], Parallelize, Identity] ;
    sm$print = If[OptionValue["Verbose"], Print, Nothing] ;
    sm$epsilon /: sm$epsilon^sm$power_ /; sm$power > sm$degree := 0 ;
    sm$print["SQUARE MATRIX (\"DIRECT\")"] ;
    sm$print["Dimension                          :  ",sm$dimension] ;
    sm$print["Computation degree                 :  ",sm$degree] ;
    sm$print["Monomial variables                 :  ",sm$size] ;
    sm$print["Matrix dimensions                  :  ",sm$size," x ",sm$size," = ",sm$size^2] ;
    sm$print["Define local phase space variables..."] ;
    sm$variables = ToExpression[StringTemplate["z$`1`"] /@ Range[sm$dimension]] ;
    sm$print["Define monomial basis rules..."] ;
    sm$monomial /: sm$monomial[x__] * sm$monomial[y__] := sm$monomial @@ ({x} + {y}) ;
    sm$monomial /: sm$monomial[x__]^(y_) := sm$monomial @@ ({x}*y) ;
    sm$print["Generate variables transformation rules for given map..."] ;
    sm$time = AbsoluteTiming[
        sm$rules = sm$chop[map @@ (sm$epsilon*sm$variables)] ;
        sm$rules = sm$function[(Collect[#, sm$epsilon] & ) /@ sm$rules];
        sm$rules = Dispatch[Thread[sm$variables -> sm$rules]] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Substitute rules into monomials and truncate..."] ;
    sm$time = AbsoluteTiming[
        sm$list = Activate[Inactivate[sm$chop[Collect[# /. sm$rules, sm$epsilon]] & ]] ;
        sm$list = sm$function[sm$list /@ sm$monomials @@ sm$variables] ;
        sm$epsilon = 1 ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Expand monomials..."] ;
    sm$time = AbsoluteTiming[
        sm$list = sm$function[Expand /@ sm$list] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Convert to monomial basis representation..."] ;

    sm$rules = Dispatch[Thread[sm$variables -> (Apply[sm$monomial]) /@ IdentityMatrix[sm$dimension]]] ;
    sm$time = AbsoluteTiming[
        sm$list = (ReplaceAll[sm$rules]) /@ sm$list ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Compute square matrix..."] ;
    sm$time = AbsoluteTiming[
        sm$matrix = {(Apply[sm$monomial]) /@ Flatten[sm$exponents, 1]} ;
        sm$matrix = sm$chop[D[sm$list, sm$matrix]] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Return square matrix..."] ;
    SparseArray[sm$matrix]
] ;

(* ################################################################################################################## *)

sm$make$matrix[                                   (* -- make square matrix *)
    "JET",                                        (* -- "JET" computation method *)
    map_,                                         (* -- map *)
    opt:OptionsPattern[]                          (* -- option(s) *)
] := Block[
    {sm$function, sm$print, sm$time, sm$jet, sm$matrix, sm$partitions},
    sm$function = If[OptionValue["Parallelize"], Parallelize, Identity] ;
    sm$print = If[OptionValue["Verbose"], Print, Nothing] ;
    sm$print["SQUARE MATRIX (\"JET\")"] ;
    sm$print["Dimension                          :  ",sm$dimension] ;
    sm$print["Computation degree                 :  ",sm$degree] ;
    sm$print["Monomial variables                 :  ",sm$size] ;
    sm$print["Matrix dimensions                  :  ",sm$size," x ",sm$size," = ",sm$size^2] ;
    sm$print["Make jets..."] ;
    sm$time = AbsoluteTiming[
        sm$jet = sm$make$jet[map] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Set initial matrix..."] ;
    sm$matrix = sm$table ;
    sm$matrix[[Range[sm$dimension]]] = sm$jet ;
    sm$print["Set partitions..."] ;
    sm$partitions = Rest[sm$intervals] ;
    sm$print["Enter main loop..."] ;
    sm$time = AbsoluteTiming[
        Do[
            Block[
                {sm$range, sm$pair},
                sm$print[StringTemplate["Now computing order `1`..."][1 + First[Flatten[Position[sm$partitions, sm$loop]]]]] ;
                sm$time = AbsoluteTiming[
                    sm$range = Range @@ sm$loop ;
                    sm$pair = sm$matrix[[sm$range]] ;
                    sm$pair = Partition[Flatten[sm$pair], 1] ;
                    sm$pair = Partition[Extract[sm$matrix, sm$pair], 2] ;
                    sm$pair = sm$function[Expand @* sm$mult /@ sm$pair] ;
                    sm$matrix[[sm$range]] = sm$pair ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
            ],
            {sm$loop, sm$partitions}
        ] ;
    ] ;
    sm$print["Exit main loop..."] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Return square matrix..."] ;
    SparseArray[sm$chop[sm$matrix]]
] ;

(* ################################################################################################################## *)

sm$make$matrix[                                   (* -- make square matrix *)
    "OPTIMIZED",                                  (* -- "OPTIMIZED" computation method *)
    map_,                                         (* -- map *)
    opt:OptionsPattern[]                          (* -- option(s) *)
] := Block[
    {sm$function, sm$print, sm$time, sm$jet, sm$matrix, sm$partitions},
    sm$function = If[OptionValue["Parallelize"], Parallelize, Identity] ;
    sm$print = If[OptionValue["Verbose"], Print, Nothing] ;
    sm$print["SQUARE MATRIX (\"OPTIMIZED\")"] ;
    sm$print["Dimension                          :  ",sm$dimension] ;
    sm$print["Computation degree                 :  ",sm$degree] ;
    sm$print["Monomial variables                 :  ",sm$size] ;
    sm$print["Matrix dimensions                  :  ",sm$size," x ",sm$size," = ",sm$size^2] ;
    sm$print["Make jets..."] ;
    sm$time = AbsoluteTiming[
        sm$jet = sm$make$jet[map] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Set initial matrix..."] ;
    sm$matrix = sm$table ;
    sm$matrix[[Range[sm$dimension]]] = sm$jet ;
    sm$print["Set partitions..."] ;
    sm$partitions = Rest[sm$intervals] ;
    sm$print["Enter main loop..."] ;
    sm$time = AbsoluteTiming[
        Do[
            Block[
                {sm$order, sm$range, sm$pair},
                sm$order = 1 + First[Flatten[Position[sm$partitions, sm$loop]]] ;
                sm$print[StringTemplate["Now computing order `1`..."][sm$order]] ;
                sm$time = AbsoluteTiming[
                    sm$range = Apply[Range, sm$loop] ;
                    sm$pair = sm$matrix[[sm$range]] ;
                    sm$pair = MapAt[sm$matrix[[#]] & , sm$pair, {All, -1}] ;
                    sm$pair = (sm$mult$optimized[First[#]][sm$order][Last[#]] & ) /@ sm$pair ;
                    sm$pair = Expand /@ sm$pair ;
                    sm$matrix[[sm$range]] = sm$pair ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
            ],
            {sm$loop, sm$partitions}
        ] ;
    ] ;
    sm$print["Exit main loop..."] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Return square matrix..."] ;
    SparseArray[sm$chop[sm$matrix]]
] ;

(* ################################################################################################################## *)

sm$make$matrix[                                   (* -- make square matrix *)
    "COMPILED",                                   (* -- "COMPILED" computation method *)
    map_,                                         (* -- map *)
    opt:OptionsPattern[]                          (* -- option(s) *)
] := Block[
    {sm$function, sm$print, sm$time, sm$jet, sm$matrix, sm$partitions},
    sm$function = If[OptionValue["Parallelize"], Parallelize, Identity] ;
    sm$print = If[OptionValue["Verbose"], Print, Nothing] ;
    sm$print["SQUARE MATRIX (\"COMPILED\")"] ;
    sm$print["Dimension                          :  ",sm$dimension] ;
    sm$print["Computation degree                 :  ",sm$degree] ;
    sm$print["Monomial variables                 :  ",sm$size] ;
    sm$print["Matrix dimensions                  :  ",sm$size," x ",sm$size," = ",sm$size^2] ;
    sm$print["Make jets..."] ;
    sm$time = AbsoluteTiming[
        sm$jet = sm$make$jet[map] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Set initial matrix..."] ;
    sm$matrix = sm$table ;
    sm$matrix[[Range[sm$dimension]]] = sm$jet ;
    sm$print["Set partitions..."] ;
    sm$partitions = Rest[sm$intervals] ;
    sm$print["Enter main loop..."] ;
    sm$time = AbsoluteTiming[
        Do[
            Block[
                {sm$range, sm$pair},
                sm$print[StringTemplate["Now computing order `1`..."][1 + First[Flatten[Position[sm$partitions, sm$loop]]]]] ;
                sm$time = AbsoluteTiming[
                    sm$range = Range @@ sm$loop ;
                    sm$pair = sm$matrix[[sm$range]] ;
                    sm$pair = Partition[Flatten[sm$pair], 1] ;
                    sm$pair = Partition[Extract[sm$matrix, sm$pair], 2] ;
                    sm$pair = sm$mult$compiled[sm$pair] ; ;
                    sm$matrix[[sm$range]] = sm$pair ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
            ],
            {sm$loop, sm$partitions}
        ] ;
    ] ;
    sm$print["Exit main loop..."] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Return square matrix..."] ;
    SparseArray[sm$chop[sm$matrix]]
] ;

(* ################################################################################################################## *)
(* SQUARE MATRIX VISUALIZATION *)
(* ################################################################################################################## *)

ClearAll[sm$matrix$plot] ;

sm$matrix$plot::usage = "sm$matrix$plot[matrix] -- visual representation of numerical square matrix <mat> " ;

sm$matrix$plot[                                   (* -- visual representation of numerical square matrix *)
    matrix_,                                      (* -- numerical square matrix *)
    opt:OptionsPattern[ArrayPlot]                 (* -- plot options *)
] := Block[
    {sm$data, sm$partitions, sm$color},
    sm$data = Sign[Abs[matrix]] ;
    sm$partitions = Transpose[ConstantArray[Transpose[{ConstantArray[1, Length[sm$counts]], Accumulate[sm$counts]}], 2]] ;
    sm$data = Total[(SparseArray[Take[sm$data, Sequence @@ #], {sm$size, sm$size}] & ) /@ sm$partitions] ;
    sm$color = Flatten[ConstantArray[{Red, Blue}, 1 + Length[sm$counts]]] ;
    sm$color = Join[{0 -> White}, Thread[Range[Length[sm$counts]] -> Take[sm$color, {1, Length[sm$counts]}]]] ;
    ArrayPlot[
        sm$data,
        ColorRules -> sm$color,
        opt,
        FrameTicks -> {False, False, True, True}
    ]
] ;

(* ################################################################################################################## *)
(* TRANSFROM MONOMIALS *)
(* ################################################################################################################## *)

ClearAll[sm$transform$monomials] ;

sm$transform$monomials::usage = "sm$transform$monomials[monomial,transformation] -- linear transformation of monomials " ;

sm$transform$monomials[                           (* -- linear transformation of monomials *)
    monomial_,                                    (* -- monomial function *)
    transformation_                               (* -- transformation rules *)
] := Block[
    {sm$variables, sm$rules, sm$output},
    sm$variables = First[monomial] ;
    sm$rules = Dispatch[transformation @@ sm$variables] ;
    sm$output = Expand @* (ReplaceAll[sm$rules]) /@ monomial @@ sm$variables ;
    Function @@ {sm$variables, sm$output}
] ;

(* ################################################################################################################## *)
(* COUNT MULTIPLICITY *)
(* ################################################################################################################## *)

ClearAll[sm$count$dimension] ;

sm$count$dimension::usage = "sm$count$dimension[value,matrix] -- count multiplicity of given eigenvalue <value> and square matrix <matrix> " ;

sm$count$dimension[                               (* -- count invariant subspace dimension for given eigenvalue *)
    value_,                                       (* -- eigenvalue *)
    matrix_                                       (* -- square matrix *)
] := If[
    NumberQ[value],
    Count[Abs[sm$chop[Normal[Diagonal[matrix]] - value]], 0],
    Count[Normal[Diagonal[matrix]], value]
] ;

(* ################################################################################################################## *)
(* COMPUTE EIGENVECTORS *) 
(* ################################################################################################################## *)

ClearAll[sm$make$vectors] ;

sm$make$vectors::usage = "sm$make$vectors[value, matrix] -- make left eigenvectors for given eigenvalue <value> and square matrix <matrix> " ;

Options[sm$make$vectors] = {
    "Verbose" -> False,                           (* -- verbose flag *)
    "BLAS" -> True,                               (* -- flag to use BLAS TRSV solver *)
    "Method" -> Automatic                         (* -- linear solve method if not BLAS *)
} ;

sm$make$vectors[                                  (* -- make left eigenvectors *)
    value_,                                       (* -- selected eigenvalue *)
    matrix_,                                      (* -- square matrix *)
    opt:OptionsPattern[]                          (* -- option(s) *)
] := Block[
    {sm$print, sm$time, sm$positions, sm$multiplicity, sm$matrix, sm$order, sm$range, sm$invariant, sm$vec, sm$vectors, sm$factors, sm$jordan, sm$normal, sm$partitions, sm$parameters, sm$variables, sm$local, sm$rhs, sm$lhs, sm$system},
    sm$print = If[OptionValue["Verbose"], Print, Nothing] ;
    sm$positions = If[
        NumberQ[value],
        Flatten[Position[Abs[sm$chop[Normal[Diagonal[matrix]] - value]], 0]],
        Flatten[Position[Normal[Diagonal[matrix]], value]]
    ] ;
    sm$multiplicity = Length[sm$positions] ;
    sm$matrix = Normal[matrix] ;
    sm$order =  First[Flatten[Position[(IntervalMemberQ[Interval[#], First[sm$positions]] &) /@ sm$intervals, True]]] ;
    sm$range = Range[sm$order, sm$degree, 2] ;
    sm$invariant = Length[sm$range] ;
    sm$print["Chop delta parameter               :  ", sm$delta] ;
    sm$print["Phase space dimension              :  ", sm$dimension] ;
    sm$print["Computation degree                 :  ", sm$degree] ;
    sm$print["Square matrix dimensions           :  ", StringRiffle[ToString /@ {sm$size, sm$size}, " x "]," = ",sm$size^2] ;
    sm$print["Number of nonzero matrix elements  :  ", Length[ArrayRules[SparseArray[sm$matrix]]] - 1," (",100*SparseArray[sm$matrix]["Density"]," %)"] ;
    sm$print["Selected eigenvalue                :  ", value] ;
    sm$print["Eigenvalue multiplicity            :  ", sm$multiplicity] ;
    sm$print["First vector leading degree        :  ", sm$order] ;
    sm$print["Invariant dimension                :  ", sm$invariant] ;
    sm$print["Define vectors..."] ;
    sm$vectors = Array[sm$vec, {sm$invariant, sm$size}] ;
    sm$print["Set zero and arbitrary components..."] ;
    sm$vectors = (TakeList[#, sm$counts] & ) /@ sm$vectors ;
    sm$factors = ConstantArray[1, sm$degree] ;
    sm$factors = (PadLeft[Take[sm$factors, {# + 1, sm$degree}], sm$degree] & ) /@ sm$range ;
    sm$vectors = Flatten /@ (sm$factors*sm$vectors) ;
    sm$vectors[[1, sm$positions]] = PadRight[{1}, Length[sm$positions]] ;
    sm$positions = (Pick[sm$positions, Thread[sm$positions >= sm$intervals[[#, 1]]], True] & ) /@ Rest[sm$range] ;
    Block[
        {sm$index},
        sm$index = sm$positions[[#]] ;
        sm$index = Transpose[{ConstantArray[#, Length[sm$index]], sm$index}] ;
        sm$index = (Apply[sm$vec]) /@ sm$index; sm$vectors[[# + 1, sm$positions[[#]]]] = sm$index
    ] & /@ Range[sm$invariant - 1] ;
    sm$print["Number of zero vector components   :  ", {Count[Flatten[sm$vectors], 0], Length[Flatten[sm$vectors]]}] ;
    sm$print["Distribution of zero components    :  ", Transpose[{Range[sm$invariant], Count[0] /@ sm$vectors}]] ;
    sm$print["Define Jordan block for effective invariant subspace dimension..."] ;
    sm$jordan = Normal[SparseArray[Thread[Rest[NestList[1 + # & , {0, 1}, sm$invariant - 1]] -> 1], {sm$invariant, sm$invariant}]] ;
    sm$print["Define normal form matrix..."] ;
    sm$normal = sm$chop[MatrixExp[I*ComplexExpand[Im[PowerExpand[Log[value]]]]*IdentityMatrix[sm$invariant] + sm$jordan]] ;
    sm$print["Normal form matrix dimensions      :  ", Dimensions[sm$normal]] ;
    sm$print["Compute dot product of normal form matrix and left eigenvectors..."] ;
    sm$time = AbsoluteTiming[
         sm$normal = sm$chop[sm$normal . sm$vectors] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Define vectors and matrix partitions..."] ;
    sm$partitions = {sm$intervals, Transpose[{ConstantArray[1, sm$degree], Last[Transpose[sm$intervals]]}]} ;
    sm$print["Define variables grouped by degree..."] ;
    sm$parameters = Transpose[(TakeList[#, sm$counts] & ) /@ sm$vectors] ;
    sm$parameters = (Sort[Cases[#, sm$vec[__], Infinity]] & ) /@ sm$parameters ;
    sm$print["Find vector components degree-by-degree..."] ;
    sm$time = AbsoluteTiming[
        Do[
            {
                sm$print["Current degree                     :  ", sm$loop, "/", sm$degree] ;
                sm$variables = sm$parameters[[sm$loop]] ;
                sm$print["Number of variables                :  ", Length[sm$variables]] ;
                If[
                    sm$variables === {},
                    Continue[]
                ] ;
                sm$print["Generate linear system..."] ;
                sm$time = AbsoluteTiming[
                    sm$local = Take[sm$vectors, All, sm$partitions[[2, sm$loop]]] ;
                    sm$rhs = Take[sm$matrix, Sequence @@ Reverse[sm$partitions[[All, sm$loop]]]] ;
                    sm$rhs = sm$local . sm$rhs ;
                    sm$lhs = Take[sm$normal, All, sm$partitions[[1, sm$loop]]] ;
                    sm$system = Flatten[sm$chop[sm$rhs - sm$lhs], 1] ;
                    sm$system = DeleteCases[sm$system, 0] ;
                    sm$print["Number of equations                :  ", Length[sm$system]] ;
                    If[
                        Length[sm$variables] =!= Length[sm$system],
                        Break[]
                    ] ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
                sm$print["Generate matrix..."] ;
                sm$time = AbsoluteTiming[
                    sm$lhs = sm$chop[D[sm$system, {sm$variables}]] ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
                sm$print["Generate vector..."] ;
                sm$time = AbsoluteTiming[
                    sm$rhs = sm$chop[- sm$system /. Dispatch[Thread[sm$variables -> 0]]] ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
                sm$print["Solve linear system..."] ;
                sm$time = AbsoluteTiming[
                    If[
                        OptionValue["BLAS"],
                        LinearAlgebra`BLAS`TRSV["U", "N", "N", sm$lhs, sm$rhs],
                        sm$rhs = LinearSolve[sm$lhs, sm$rhs, Method -> OptionValue["Method"]]
                    ] ;
                    sm$rhs = sm$chop[Composition[Together, Cancel] /@ sm$rhs] ;
                    Set @@ {sm$variables, sm$rhs} ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
            },
            {sm$loop, 1, sm$degree}
        ] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Return vectors..."] ;
    sm$chop[sm$vectors]
] ;

(* ################################################################################################################## *)
(* COMPUTE EIGENVECTORS FOR EIGENVALUE ONE (INVARIANT) *)
(* NOTE, CORRECPONDS TO THE FIRST VECTOR FROM sm$make$vectors WITH 1 AS INPUT EIGENVALUE *)
(* CAN FAIL FOR PURE SYMBOLIC INPUT *)
(* ################################################################################################################## *)

ClearAll[sm$make$vectors$one] ;

sm$make$vectors$one::usage = "sm$make$vectors$one[matrix] -- make left eigenvectors for eigenvalue 1 and square matrix <matrix> " ;

Options[sm$make$vectors$one] = {
    "Verbose" -> False,                           (* -- verbose flag *)
    "BLAS" -> True,                               (* -- flag to use BLAS TRSV solver *)
    "Method" -> Automatic                         (* -- linear solve method if not BLAS *)
} ;

sm$make$vectors$one[                              (* -- make left eigenvectors *)
    matrix_,                                      (* -- square matrix *)
    opt:OptionsPattern[]                          (* -- option(s) *)
] := Block[
    {sm$print, sm$time, sm$positions, sm$matrix, sm$vec, sm$vectors, sm$jordan, sm$normal, sm$partitions, sm$parameters, sm$variables, sm$local, sm$rhs, sm$lhs, sm$system},
    sm$print = If[OptionValue["Verbose"], Print, Nothing] ;
    sm$positions = Flatten[Position[Abs[sm$chop[Normal[Diagonal[matrix]]- 1]], 0]] ;
    sm$matrix = Normal[matrix] ;
    sm$print["Chop delta parameter               :  ", sm$delta] ;
    sm$print["Phase space dimension              :  ", sm$dimension] ;
    sm$print["Computation degree                 :  ", sm$degree] ;
    sm$print["Square matrix dimensions           :  ", StringRiffle[ToString /@ {sm$size, sm$size}, " x "], " = ", sm$size^2] ;
    sm$print["Number of nonzero matrix elements  :  ", Length[ArrayRules[SparseArray[sm$matrix]]] - 1, " (", 100*SparseArray[sm$matrix]["Density"], " %)"] ;
    sm$print["Selected eigenvalue                :  ", 1]; sm$print["Define vector..."] ;
    sm$vectors = Array[sm$vec, sm$size] ;
    sm$print["Set zero and arbitrary components..."] ;
    sm$vectors[[sm$positions]] = PadRight[{1}, Length[sm$positions]] ;
    sm$vectors[[Range[1, First[sm$positions] - 1]]] = 0 ;
    sm$vectors[[Last /@ Cases[First[Rest[TakeList[sm$vectors, sm$counts]]], sm$vec[__]]]] = 0 ;
    sm$print["Number of zero vector components   :  ", {Count[Flatten[sm$vectors], 0], Length[Flatten[sm$vectors]]}] ;
    sm$print["Define normal form vector..."] ;
    sm$normal = sm$vectors ;
    sm$print["Define vectors and matrix partitions..."] ;
    sm$partitions = {sm$intervals, Transpose[{ConstantArray[1, sm$degree], Last[Transpose[sm$intervals]]}]} ;
    sm$print["Define variables grouped by degree..."] ;
    sm$parameters = TakeList[sm$vectors, sm$counts] ;
    sm$parameters = (Sort[Cases[#, sm$vec[__], Infinity]] & ) /@ sm$parameters ;
    sm$print["Find vector components degree-by-degree..."] ;
    sm$time = AbsoluteTiming[
        Do[
            {
                sm$print["Current degree                     :  ", sm$loop, "/", sm$degree] ;
                sm$variables = sm$parameters[[sm$loop]] ;
                sm$print["Number of variables                :  ", Length[sm$variables]] ;
                If[
                    sm$variables === {},
                    Continue[]
                ] ;
                sm$print["Generate linear system..."] ;
                sm$time = AbsoluteTiming[
                    sm$local = Take[sm$vectors, sm$partitions[[2, sm$loop]]] ;
                    sm$rhs = Take[sm$matrix, Sequence @@ Reverse[sm$partitions[[All, sm$loop]]]] ;
                    sm$rhs = sm$local . sm$rhs ;
                    sm$lhs = Take[sm$normal, sm$partitions[[1,sm$loop]]] ;
                    sm$system = Flatten[sm$chop[sm$rhs - sm$lhs], 1] ;
                    sm$system = DeleteCases[sm$system, _?NumberQ] ;
                    sm$print["Number of equations                :  ", Length[sm$system]] ;
                    If[
                        Length[sm$variables] =!= Length[sm$system],
                        Break[]
                    ] ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
                sm$print["Generate matrix..."] ;
                sm$time = AbsoluteTiming[
                    sm$lhs = sm$chop[D[sm$system, {sm$variables}]] ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
                sm$print["Generate vector..."] ;
                sm$time = AbsoluteTiming[
                    sm$rhs = sm$chop[-sm$system /. Dispatch[Thread[sm$variables -> 0]]] ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
                sm$print["Solve linear system..."] ;
                sm$time = AbsoluteTiming[
                    If[
                        OptionValue["BLAS"],
                        LinearAlgebra`BLAS`TRSV["U", "N", "N", sm$lhs, sm$rhs],
                        sm$rhs = LinearSolve[sm$lhs, sm$rhs, Method -> OptionValue["Method"]] ;
                    ] ;
                    sm$rhs = sm$chop[Expand /@ sm$rhs] ;
                    Set @@ {sm$variables, sm$rhs} ;
                ] ;
                sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
            },
            {sm$loop, 1, sm$degree}
        ] ;
    ] ;
    sm$print[StringTemplate["Finished in `1` sec."][First[sm$time]]] ;
    sm$print["Return vector..."] ;
    {sm$chop[sm$vectors]}
] ;

(* ################################################################################################################## *)
(* MAKE COORDINATE *)
(* ################################################################################################################## *)

ClearAll[sm$make$coordinate] ;

sm$make$coordinate::usage = "sm$make$coordinate[monomial, variables, vector] -- make normal form eigen coordinates " ;

sm$make$coordinate[                               (* -- make normal form eigen coordinates *)
    monomial_,                                    (* -- transformed monomials function *)
    variables_,                                   (* -- list of variables to use, e.g. for 4D {qx,px,qy,py} *)
    vector_,                                      (* -- left eigenvector *)
    reduce_:True                                  (* -- flag to perform mononial expansion *)
] := If[
    reduce,
    sm$chop[Total[MonomialList[Normal[vector] . monomial @@ variables, variables]]],
    Normal[vector] . monomial @@ variables
] ;

sm$make$coordinate[monomial_,variables_][vector_] := sm$make$coordinate[monomial, variables, vector]  ;

(* ################################################################################################################## *)
(* MAKE INVARIANT AMPLITUDE -- W * conj(W) *)
(* ################################################################################################################## *)

ClearAll[sm$make$invariant] ;

ClearAll[sm$make$invariant] ;

sm$make$invariant::usage = "sm$make$invariant[degree, variables, coordinate] -- make invariant " ;

sm$make$invariant[                                (* -- make invariant (amplitude of normal form coordinate) *)
    degree_,                                      (* -- truncation degree *)
    variables_,                                   (* -- list of phase space variables *)
    coordinate_,                                  (* -- normal coordinate *)
    simplify_:Identity                            (* -- simplification function *)
] := Block[
    {sm$epsilon, sm$rule, sm$coordinate, sm$conjugate, sm$invariant},
    sm$epsilon /: sm$epsilon^(sm$power_) /; sm$power > degree := 0;
    sm$rule = Dispatch[Thread[variables -> sm$epsilon*variables]] ;
    sm$coordinate = coordinate /. sm$rule ;
    sm$conjugate = sm$coordinate /. Complex[real_, imaginary_] :> Complex[real, -imaginary] ;
    sm$invariant = Collect[sm$coordinate*sm$conjugate, sm$epsilon] ;
    sm$epsilon = 1 ;
    Function @@ {variables, Total[simplify /@ MonomialList[sm$invariant, variables]]}
] ;

sm$make$invariant[degree_, variables_][coordinate_] := sm$make$invariant[degree, variables, coordinate] ;

(* ################################################################################################################## *)
(* MAKE FREQUENCY (I PHI = W1/W0 = W2/W1 = ... , EQ 1.17) *)
(* NOTE: THIS CORRESPONDS TO TUNE SHIFT *)
(* ################################################################################################################## *)

ClearAll[sm$make$frequency] ;

sm$make$frequency::usage = "sm$make$frequency[degree, variables, numerator, denomenator] -- make frequency " ;

sm$make$frequency[                                (* -- compute frequency *)
    degree_,                                      (* -- truncation degree *)
    variables_,                                   (* -- list of phase space variables *)
    numerator_,                                   (* -- numerator *)
    denominator_                                  (* -- denominator *)
] := Block[
    {sm$epsilon, sm$rule, sm$frequency},
    sm$epsilon /: sm$epsilon^(sm$power_) /; sm$power > degree := 0;
    sm$rule = Dispatch[Thread[variables -> sm$epsilon*variables]] ;
    sm$frequency = -I*(numerator/denominator)/(2*Pi) ;
    sm$frequency = Collect[sm$frequency /. sm$rule, sm$epsilon] ;
    sm$epsilon = 1 ;
    Function @@ {variables, sm$chop[sm$frequency]}
] ;

(* ################################################################################################################## *)
