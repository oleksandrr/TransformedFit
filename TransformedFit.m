BeginPackage["TransformedFit`"];

ClearAll[TransformedParameter];
SetAttributes[TransformedParameter, HoldRest];

Unprotect[TransformedFit]; ClearAll[TransformedFit];

Unprotect[ComplexFit]; ClearAll[ComplexFit];

Begin["`Private`"];

(* Transform numeric quantities rather than renaming them *)
TransformedParameter[t_, num_?NumericQ] := t[num];

(* Generate unique symbols for each transformed parameter -- this avoids difficulties
caused by overzealous common subexpression elimination when the models are compiled *)
TransformedParameter[t_, p_] := TransformedParameter[t, p] =
   With[{sym = Unique["TransformedParameter$", Temporary]},
    (* Unset memo when cleared to facilitate garbage collection *)
    sym /: clear : (Clear | ClearAll | Remove)[___, sym, ___] :=
     clear /; (TransformedParameter[t, p] =.; True);
    
    (* Display as the parameter by itself if the transformation is Identity *)
    sym /: MakeBoxes[sym, form_] :=
     With[{boxes = MakeBoxes[p, form]},
       InterpretationBox[boxes, sym]
      ] /; t === Identity;
    
    sym /: MakeBoxes[sym, form_] :=
     With[{boxes = MakeBoxes[t[p], form]},
      InterpretationBox[boxes, sym]
     ];
    
    sym
   ];

ClearAll[$FitFunctions];
$FitFunctions = If[$VersionNumber >= 7,
   {FindFit, NonlinearModelFit},
   {FindFit}
  ];

Options[TransformedFit] = {
   "FitFunction" -> First[$FitFunctions],
   "Transformation" -> Identity,
   "ParameterTransformation" -> Identity,
   "Hold" -> False
  };

TransformedFit::cons = 
  "The constraint(s), `1`, should be given in terms of the transformed parameters only.";

TransformedFit[
    data_, {model_, cons_}, pars_, vars_,
    opts___
   ] /; Internal`DependsOnQ[cons, pars] :=
  Message[TransformedFit::cons, cons];

(* Deal with data given as ordinate values only *)
TransformedFit[
   data_?VectorQ, model_, pars_, vars_,
   opts : OptionsPattern[{TransformedFit, Sequence @@ $FitFunctions}]
  ] :=
  TransformedFit[
   Transpose[{Range@Length[data], data}], model, pars, vars,
   opts
  ];

TransformedFit[
   data_?MatrixQ, {model_, cons_} | {model_} | model_, pars_, vars_,
   opts : OptionsPattern[{TransformedFit, Sequence @@ $FitFunctions}]
  ] :=
  With[{
    fitFunction = If[MemberQ[$FitFunctions, #], #, First[$FitFunctions]] & @ OptionValue["FitFunction"],
    transformations = List@OptionValue["Transformation"]~Flatten~1
   },
   Block[{
     transformedData,
     transformedParameters, unusedParameterMask, parameterRules,
     transformedModel,
     i
    },
    (* TRANSFORM DATA *)
    With[{
      abscissae = Take[data, All, {1, -2}],
      ordinates = Take[data, All, {-1}]
     },
     transformedData = {
         ConstantArray[Range@Length[transformations], {Length[abscissae], 1}]~Transpose~{2, 3, 1},
         ConstantArray[abscissae, Length[transformations]],
         Through@transformations[ordinates]
        }~Flatten~{{2, 3}, {1, 4}};
     ];
    
    (* TRANSFORM PARAMETERS *)
    transformedParameters = Outer[
       TransformedParameter,
       transformations, {pars}~Flatten~1
      ] // Transpose;
    With[{
      (* Original and transformed parameters without initial guesses *)
      originalParameterNames = Replace[pars, {p_, __?NumericQ} :> p, {1}],
      transformedParameterNames = Replace[transformedParameters, {p_, __?NumericQ} :> p, {2}]
     },
     With[{
        (* Representations of the original parameters in terms of their transformations *)
        parameterRepresentations = OptionValue["ParameterTransformation"] @@@ transformedParameterNames
       },
       unusedParameterMask = MapThread[
         Composition[Thread, Unevaluated, FreeQ],
         {parameterRepresentations, transformedParameterNames}
        ];
       Clear @@  Flatten@Pick[transformedParameterNames, unusedParameterMask];
       parameterRules = Thread[originalParameterNames -> parameterRepresentations];
      ];
    ];
    
    (* TRANSFORM MODEL *)
    With[{
      reparameterizedModel = model /. parameterRules,
      KroneckerDelta = If[Equal[##], 1, 0] & (* compilable *)
     },
     transformedModel = Inner[
        #1[reparameterizedModel] KroneckerDelta[i, #2] &,
        transformations, Range@Length[transformations]
       ];
    ];
    
    (* PERFORM FIT *)
    If[TrueQ@OptionValue["Hold"], Composition[Hold, fitFunction], fitFunction][
     transformedData,
     {transformedModel, cons},
     Pick[transformedParameters, unusedParameterMask, False]~Flatten~1,
     {i, vars}~Flatten~1,
     FilterRules[{opts}, Options[fitFunction]]
    ]
   ]
  ];

Protect[TransformedFit];

ClearAll[coordinateSystemRules];
coordinateSystemRules["Cartesian"] = Sequence[
   "Transformation" -> {Re, Im},
   "ParameterTransformation" -> (#1 + I #2 &)
  ];
coordinateSystemRules["Polar"] = Sequence[
   "Transformation" -> {Abs, Arg},
   "ParameterTransformation" -> (#1 Exp[I #2] &)
  ];
coordinateSystemRules["Real"] = Sequence[
   "Transformation" -> {Re, Im},
   "ParameterTransformation" -> (#1 &)
  ];
coordinateSystemRules["Imaginary"] = Sequence[
   "Transformation" -> {Re, Im},
   "ParameterTransformation" -> (I #2 &)
  ];
(* Default to Cartesian coordinates *)
coordinateSystemRules[_] = coordinateSystemRules["Cartesian"];

Options[ComplexFit] = {
   "CoordinateSystem" -> Automatic
  };

ComplexFit[
   data_, model_, pars_, vars_,
   opts : OptionsPattern[{ComplexFit, TransformedFit, Sequence @@ $FitFunctions}]
  ] :=
  TransformedFit[
   data, model, pars, vars,
   coordinateSystemRules@OptionValue["CoordinateSystem"],
   FilterRules[{opts}, Except["CoordinateSystem" | "Transformation" | "ParameterTransformation"]]
  ];

Protect[ComplexFit];

End[];

EndPackage[];
