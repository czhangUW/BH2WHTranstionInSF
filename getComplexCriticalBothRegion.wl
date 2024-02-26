(* ::Package:: *)

sfDataFromBmToBmp[curvedSFData_,rule4Bp_,futureTetrahedra_]:=Block[{gzRule,areaRule,bdyspinors,orientingTrigsInBp,allOrientatedTriangle,orientedTrig0,orientedTrig1,epVef},
 gzRule=curvedSFData[[1]]//Normal;
gzRule={gzRule,gzRule/.rule4Bp}//Flatten//Dispatch;
areaRule=curvedSFData[[2]]//Normal;
areaRule={areaRule,areaRule/.rule4Bp}//Flatten//DeleteDuplicates//Dispatch;
bdyspinors=curvedSFData[[3]]//Normal;
bdyspinors=GroupBy[bdyspinors,IntersectingQ[Keys[#],futureTetrahedra]&][False];
bdyspinors={bdyspinors,bdyspinors/.rule4Bp}//Flatten//DeleteDuplicates//Dispatch;
orientingTrigsInBp=curvedSFData[[4]]//Association;
orientingTrigsInBp=Reverse/@orientingTrigsInBp;
orientingTrigsInBp=RotateLeft/@orientingTrigsInBp//Normal;
orientingTrigsInBp=orientingTrigsInBp/.rule4Bp;
allOrientatedTriangle={curvedSFData[[4]],orientingTrigsInBp}//Flatten;
allOrientatedTriangle=GroupBy[allOrientatedTriangle,Keys]//Values;
allOrientatedTriangle=GroupBy[allOrientatedTriangle,Length];
{orientedTrig0,orientedTrig1}={allOrientatedTriangle[1],allOrientatedTriangle[2]};
orientedTrig0=Flatten[orientedTrig0];
orientedTrig1=GroupBy[Flatten[orientedTrig1],Keys,(Most/@Values[#])&];
orientedTrig1=If[#[[1,-1,2]]===#[[2,1,2]],#,Reverse[#]]&/@orientedTrig1;
(*[#[[1,-1,2]]===#[[2,1,2]] implies that the order of (v,e) is compatible with the orientaiton of the face;
Here {#[[1,-1,2]],#[[2,1,2]]} gives the last tetrahedra of the first sequence of (v,e) and the first tetrahedra of the second sequence of (v,e);
if #[[1,-1,2]]=!=#[[2,1,2]], we get that the two sequences are given by {...(v,e)},{{v',e'},...}
*)
Print["do the tetrahedra surrounding the future triangles in  B_+ and B_- connect well? ",#[[1,-1,2]]===#[[2,1,2]]&/@orientedTrig1];
orientedTrig1=Flatten[#,1]&/@orientedTrig1;
orientedTrig1=If[DuplicateFreeQ[{#[[1,2]],#[[-1,2]]}],Append[#,"boundary"],Append[RotateLeft[#],"internal"]]&/@orientedTrig1;
Print["do the tetrahedra surrounding the future internal triangles form a loop? ",#[[1,1]]==#[[-2,1]]&/@Select[orientedTrig1,Last[#]=="internal"&]];
orientedTrig1=orientedTrig1//Normal;
allOrientatedTriangle={orientedTrig0,orientedTrig1}//Flatten;
epVef=curvedSFData[[5]]//Normal;
epVef=epVef/.rule4Bp//Association;
epVef=-#&/@epVef;
epVef={curvedSFData[[5]]//Normal,epVef//Normal}//Flatten//Dispatch;
{gzRule,areaRule,bdyspinors,allOrientatedTriangle,epVef}]


checkSignIntKPho0[curvedSFData_,sl2cRules4_,spinorRules4_,allvariables_,rule4Bp_,dihedralFromCurvedGeo_]:=Block[{phi0rule,allPhiFromIntK,dihedral0,allBdyTrigsAtTransitionSurf,signDiff},
phi0rule=getFlatCoherentPhi0[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,Rule[#,0]&/@allvariables//Dispatch];
allPhiFromIntK=KeyMap[#/.rule4Bp&,dihedralFromCurvedGeo];
allPhiFromIntK=-#&/@allPhiFromIntK;
allPhiFromIntK=Join[allPhiFromIntK,dihedralFromCurvedGeo];
dihedral0=Coefficient[#,Immirzi]&/@phi0rule;
dihedral0=-dihedral0;(*Since by our definition phi=(twist angle) - Immirzi (dihedral angle). *)
dihedral0=Chop[#,10^-chopdelta]&/@dihedral0;
allBdyTrigsAtTransitionSurf=dihedral0;
allBdyTrigsAtTransitionSurf=KeySelect[allBdyTrigsAtTransitionSurf,!MemberQ[Keys[allPhiFromIntK],#]&];
allPhiFromIntK=Join[allPhiFromIntK,allBdyTrigsAtTransitionSurf];
signDiff=Merge[{dihedral0,allPhiFromIntK},Abs[(Sign[#[[2]]]-Sign[#[[1]]])]&];
signDiff=AllTrue[signDiff,#<=1&];
Print["that the signs of IntK matches the sign of phi0 is ---->",signDiff]
]


findSolutions[curvedSFData_,sl2cRules4_,spinorRules4_,areafRule_,{areaVariables_,spinSl2cVariables_},rule4Bp_,dihedralFromCurvedGeo_,scaleDPhi_,initialdataRule:{_Rule..}|{},ImmirziValue_,fileName_String,checkFlateSolQ_:False]:=
Block[{phi0rule,allPhiFromIntK,allBdyTrigsAtTransitionSurf,dihedral0,alpharule,area0Rule,dividedAreaRule,coherenStatePhase,totalActionExpression,areaequas,dividedArea,spinorSl2cEquas,areaInvolvedInEq,alleqs,allvariables,allvariablesValue,sol,actionValue,checkEq,timing,stepn,alleqsp},
allvariables={areaVariables,spinSl2cVariables}//Flatten;
phi0rule=getFlatCoherentPhi0[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,Rule[#,0]&/@allvariables//Dispatch];
allPhiFromIntK=KeyMap[#/.rule4Bp&,dihedralFromCurvedGeo];
allPhiFromIntK=-#&/@allPhiFromIntK;
allPhiFromIntK=Join[allPhiFromIntK,dihedralFromCurvedGeo];
dihedral0=Coefficient[#,Immirzi]&/@phi0rule;
dihedral0=-dihedral0;(*Since by our definition phi=(twist angle) - Immirzi (dihedral angle). *)
allBdyTrigsAtTransitionSurf=dihedral0;
allBdyTrigsAtTransitionSurf=KeySelect[allBdyTrigsAtTransitionSurf,!MemberQ[Keys[allPhiFromIntK],#]&];
allPhiFromIntK=Join[allPhiFromIntK,allBdyTrigsAtTransitionSurf];
phi0rule=Merge[{phi0rule,allPhiFromIntK,dihedral0},#[[1]]-(#[[2]]-#[[3]])Immirzi scaleDPhi&];
alpharule=getCoherentSpread[curvedSFData[[4]],If[#[[1]]===#[[2]],1,0]&];
coherenStatePhase=getbdyCoherentStatePhase[curvedSFData[[4]],areafRule,phi0rule,alpharule]//Expand;
totalActionExpression=actionTotal[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,areafRule,coherenStatePhase];
totalActionExpression=totalActionExpression/.Immirzi->ImmirziValue//N[#,precise]&;
(***used latter**)
area0Rule=(areafRule//Normal)/.Subscript[areaj,_]:>0//Association;
dividedAreaRule=area0Rule;
dividedAreaRule=KeyMap[areaj@@#&,dividedAreaRule];
(*****)
areaequas=D[totalActionExpression,{areaVariables}];
dividedArea=areaVariables/.dividedAreaRule;
areaequas=areaequas/dividedArea;
spinorSl2cEquas=D[totalActionExpression,{spinSl2cVariables}];
areaInvolvedInEq=Cases[#,Subscript[areaj,_],Infinity]&/@spinorSl2cEquas;
areaInvolvedInEq=areaInvolvedInEq/.dividedAreaRule;
areaInvolvedInEq=Max/@areaInvolvedInEq;
spinorSl2cEquas=spinorSl2cEquas/areaInvolvedInEq;
alleqs=Join[areaequas,spinorSl2cEquas];
If[checkFlateSolQ,checkEq=alleqs/.(allvariables->0//Thread//Dispatch)//Chop[#,10^-chopdelta]&;
checkEq=Position[checkEq,_?(#!=0&)]//Flatten;
checkEq=allvariables[[checkEq]];
Return[checkEq]
];
allvariablesValue=If[initialdataRule==={},{#,0}&/@allvariables,List@@@initialdataRule];
stepn=0;
{timing,sol}=FindRoot[alleqs,allvariablesValue,WorkingPrecision->30,EvaluationMonitor:>(stepn++;Print[{stepn,alleqs//Abs//Max}])]//AbsoluteTiming;
Print[timing];
If[!MatchQ[sol,{_Rule..}],Return["Wrong Happens"]];
alleqsp=D[totalActionExpression,{allvariables}];
checkEq={alleqs,alleqsp}/.Dispatch[sol];
checkEq=Max/@Abs/@checkEq;
actionValue=totalActionExpression/.Dispatch[sol];
Export[fileName<>".wl",{checkEq,actionValue,ImmirziValue,scaleDPhi,sol}];
sol
]


(**The difference from the above one is that in this findSolutions we put {workingprecise_,accuracyGoal_} as a parameter to control the error**)
findSolutions[curvedSFData_,sl2cRules4_,spinorRules4_,areafRule_,{areaVariables_,spinSl2cVariables_},rule4Bp_,dihedralFromCurvedGeo_,scaleDPhi_,initialdataRule:{_Rule..}|{},ImmirziValue_,fileName_String,checkFlateSolQ_,{workingprecise_,accuracyGoal_,preciseGoal_}]:=
Block[{phi0rule,allPhiFromIntK,allBdyTrigsAtTransitionSurf,dihedral0,alpharule,area0Rule,dividedAreaRule,coherenStatePhase,totalActionExpression,areaequas,dividedArea,spinorSl2cEquas,areaInvolvedInEq,alleqs,allvariables,allvariablesValue,sol,actionValue,checkEq,timing,stepn,alleqsp},
allvariables={areaVariables,spinSl2cVariables}//Flatten;
phi0rule=getFlatCoherentPhi0[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,Rule[#,0]&/@allvariables//Dispatch];
allPhiFromIntK=KeyMap[#/.rule4Bp&,dihedralFromCurvedGeo];
allPhiFromIntK=-#&/@allPhiFromIntK;
allPhiFromIntK=Join[allPhiFromIntK,dihedralFromCurvedGeo];
dihedral0=Coefficient[#,Immirzi]&/@phi0rule;
dihedral0=-dihedral0;(*Since by our definition phi=(twist angle) - Immirzi (dihedral angle). *)
allBdyTrigsAtTransitionSurf=dihedral0;
allBdyTrigsAtTransitionSurf=KeySelect[allBdyTrigsAtTransitionSurf,!MemberQ[Keys[allPhiFromIntK],#]&];
allPhiFromIntK=Join[allPhiFromIntK,allBdyTrigsAtTransitionSurf];
phi0rule=Merge[{phi0rule,allPhiFromIntK,dihedral0},#[[1]]-(#[[2]]-#[[3]])Immirzi scaleDPhi&];
alpharule=getCoherentSpread[curvedSFData[[4]],If[#[[1]]===#[[2]],1,0]&];
coherenStatePhase=getbdyCoherentStatePhase[curvedSFData[[4]],areafRule,phi0rule,alpharule]//Expand;
totalActionExpression=actionTotal[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,areafRule,coherenStatePhase];
totalActionExpression=totalActionExpression/.Immirzi->ImmirziValue//N[#,precise]&;
(***used latter**)
area0Rule=(areafRule//Normal)/.Subscript[areaj,_]:>0//Association;
dividedAreaRule=area0Rule;
dividedAreaRule=KeyMap[areaj@@#&,dividedAreaRule];
(*****)
areaequas=D[totalActionExpression,{areaVariables}];
dividedArea=areaVariables/.dividedAreaRule;
areaequas=areaequas/dividedArea;
spinorSl2cEquas=D[totalActionExpression,{spinSl2cVariables}];
areaInvolvedInEq=Cases[#,Subscript[areaj,_],Infinity]&/@spinorSl2cEquas;
areaInvolvedInEq=areaInvolvedInEq/.dividedAreaRule;
areaInvolvedInEq=Max/@areaInvolvedInEq;
spinorSl2cEquas=spinorSl2cEquas/areaInvolvedInEq;
alleqs=Join[areaequas,spinorSl2cEquas];
If[checkFlateSolQ,checkEq=alleqs/.(allvariables->0//Thread//Dispatch)//Chop[#,10^-chopdelta]&;
checkEq=Position[checkEq,_?(#!=0&)]//Flatten;
checkEq=allvariables[[checkEq]];
Return[checkEq]
];
allvariablesValue=If[initialdataRule==={},{#,0}&/@allvariables,List@@@initialdataRule];
stepn=0;
{timing,sol}=FindRoot[alleqs,allvariablesValue,WorkingPrecision->workingprecise,AccuracyGoal->accuracyGoal,PrecisionGoal->preciseGoal,EvaluationMonitor:>(stepn++;Print[{stepn,alleqs//Abs//Max}])]//AbsoluteTiming;
Print[timing];
If[!MatchQ[sol,{_Rule..}],Return["Wrong Happens"]];
alleqsp=D[totalActionExpression,{allvariables}];
checkEq={alleqs,alleqsp}/.Dispatch[sol];
checkEq=Max/@Abs/@checkEq;
actionValue=totalActionExpression/.Dispatch[sol];
Export[fileName<>".wl",{checkEq,actionValue,ImmirziValue,scaleDPhi,sol}];
sol
]


findSolutionsWithCondition[curvedSFData_,sl2cRules4_,spinorRules4_,areafRule_,{areaVariables_,spinSl2cVariables_},rule4Bp_,dihedralFromCurvedGeo_,scaleDPhi_,initialdataRule:{_Rule..}|{},ImmirziValue_,fileName_String,{maxStpes_,err4Abort_}]:=
Block[{phi0rule,allPhiFromIntK,allBdyTrigsAtTransitionSurf,dihedral0,alpharule,area0Rule,dividedAreaRule,coherenStatePhase,totalActionExpression,areaequas,dividedArea,spinorSl2cEquas,areaInvolvedInEq,alleqs,allvariables,allvariablesValue,sol,actionValue,checkEq,timing,stepn,alleqsp},
allvariables={areaVariables,spinSl2cVariables}//Flatten;
phi0rule=getFlatCoherentPhi0[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,Rule[#,0]&/@allvariables//Dispatch];
allPhiFromIntK=KeyMap[#/.rule4Bp&,dihedralFromCurvedGeo];
allPhiFromIntK=-#&/@allPhiFromIntK;
allPhiFromIntK=Join[allPhiFromIntK,dihedralFromCurvedGeo];
dihedral0=Coefficient[#,Immirzi]&/@phi0rule;
dihedral0=-dihedral0;(*Since by our definition phi=(twist angle) - Immirzi (dihedral angle). *)
allBdyTrigsAtTransitionSurf=dihedral0;
allBdyTrigsAtTransitionSurf=KeySelect[allBdyTrigsAtTransitionSurf,!MemberQ[Keys[allPhiFromIntK],#]&];
allPhiFromIntK=Join[allPhiFromIntK,allBdyTrigsAtTransitionSurf];
phi0rule=Merge[{phi0rule,allPhiFromIntK,dihedral0},#[[1]]-(#[[2]]-#[[3]])Immirzi scaleDPhi&];
alpharule=getCoherentSpread[curvedSFData[[4]],If[#[[1]]===#[[2]],1,0]&];
coherenStatePhase=getbdyCoherentStatePhase[curvedSFData[[4]],areafRule,phi0rule,alpharule]//Expand;
totalActionExpression=actionTotal[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,areafRule,coherenStatePhase];
totalActionExpression=totalActionExpression/.Immirzi->ImmirziValue//N[#,precise]&;
(***used latter**)
area0Rule=(areafRule//Normal)/.Subscript[areaj,_]:>0//Association;
dividedAreaRule=area0Rule;
dividedAreaRule=KeyMap[areaj@@#&,dividedAreaRule];
(*****)
areaequas=D[totalActionExpression,{areaVariables}];
dividedArea=areaVariables/.dividedAreaRule;
areaequas=areaequas/dividedArea;
spinorSl2cEquas=D[totalActionExpression,{spinSl2cVariables}];
areaInvolvedInEq=Cases[#,Subscript[areaj,_],Infinity]&/@spinorSl2cEquas;
areaInvolvedInEq=areaInvolvedInEq/.dividedAreaRule;
areaInvolvedInEq=Max/@areaInvolvedInEq;
spinorSl2cEquas=spinorSl2cEquas/areaInvolvedInEq;
alleqs=Join[areaequas,spinorSl2cEquas];
allvariablesValue=If[initialdataRule==={},{#,0}&/@allvariables,List@@@initialdataRule];
stepn=0;
{timing,sol}=CheckAbort[FindRoot[alleqs,allvariablesValue,WorkingPrecision->30,
EvaluationMonitor:>(stepn++;Print[{stepn,alleqs//Abs//Max}];If[stepn>maxStpes&&(alleqs//Abs//Max)> err4Abort,Abort[]])],"cannot find solution in some steps"]//AbsoluteTiming;
If[sol==="cannot find solution in some steps",Return["cannot find solution in some steps"]];
Print[timing];
If[!MatchQ[sol,{_Rule..}],Return["Wrong Happens"]];
alleqsp=D[totalActionExpression,{allvariables}];
checkEq={alleqs,alleqsp}/.Dispatch[sol];
checkEq=Max/@Abs/@checkEq;
actionValue=totalActionExpression/.Dispatch[sol];
Export[fileName<>".wl",{checkEq,actionValue,ImmirziValue,scaleDPhi,sol}];
sol
]


(**The difference from the above one is that in this findSolutions we put {workingprecise_,accuracyGoal_} as a parameter to control the error**)
findSolutionsWithCondition[curvedSFData_,sl2cRules4_,spinorRules4_,areafRule_,{areaVariables_,spinSl2cVariables_},rule4Bp_,dihedralFromCurvedGeo_,scaleDPhi_,initialdataRule:{_Rule..}|{},ImmirziValue_,fileName_String,{maxStpes_,err4Abort_},{workingprecise_,accuracyGoal_,preciseGoal_}]:=
Block[{phi0rule,allPhiFromIntK,allBdyTrigsAtTransitionSurf,dihedral0,alpharule,area0Rule,dividedAreaRule,coherenStatePhase,totalActionExpression,areaequas,dividedArea,spinorSl2cEquas,areaInvolvedInEq,alleqs,allvariables,allvariablesValue,sol,actionValue,checkEq,timing,stepn,alleqsp},
allvariables={areaVariables,spinSl2cVariables}//Flatten;
phi0rule=getFlatCoherentPhi0[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,Rule[#,0]&/@allvariables//Dispatch];
allPhiFromIntK=KeyMap[#/.rule4Bp&,dihedralFromCurvedGeo];
allPhiFromIntK=-#&/@allPhiFromIntK;
allPhiFromIntK=Join[allPhiFromIntK,dihedralFromCurvedGeo];
dihedral0=Coefficient[#,Immirzi]&/@phi0rule;
dihedral0=-dihedral0;(*Since by our definition phi=(twist angle) - Immirzi (dihedral angle). *)
allBdyTrigsAtTransitionSurf=dihedral0;
allBdyTrigsAtTransitionSurf=KeySelect[allBdyTrigsAtTransitionSurf,!MemberQ[Keys[allPhiFromIntK],#]&];
allPhiFromIntK=Join[allPhiFromIntK,allBdyTrigsAtTransitionSurf];
phi0rule=Merge[{phi0rule,allPhiFromIntK,dihedral0},#[[1]]-(#[[2]]-#[[3]])Immirzi scaleDPhi&];
alpharule=getCoherentSpread[curvedSFData[[4]],If[#[[1]]===#[[2]],1,0]&];
coherenStatePhase=getbdyCoherentStatePhase[curvedSFData[[4]],areafRule,phi0rule,alpharule]//Expand;
totalActionExpression=actionTotal[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4,spinorRules4,areafRule,coherenStatePhase];
totalActionExpression=totalActionExpression/.Immirzi->ImmirziValue//N[#,precise]&;
(***used latter**)
area0Rule=(areafRule//Normal)/.Subscript[areaj,_]:>0//Association;
dividedAreaRule=area0Rule;
dividedAreaRule=KeyMap[areaj@@#&,dividedAreaRule];
(*****)
areaequas=D[totalActionExpression,{areaVariables}];
dividedArea=areaVariables/.dividedAreaRule;
areaequas=areaequas/dividedArea;
spinorSl2cEquas=D[totalActionExpression,{spinSl2cVariables}];
areaInvolvedInEq=Cases[#,Subscript[areaj,_],Infinity]&/@spinorSl2cEquas;
areaInvolvedInEq=areaInvolvedInEq/.dividedAreaRule;
areaInvolvedInEq=Max/@areaInvolvedInEq;
spinorSl2cEquas=spinorSl2cEquas/areaInvolvedInEq;
alleqs=Join[areaequas,spinorSl2cEquas];
allvariablesValue=If[initialdataRule==={},{#,0}&/@allvariables,List@@@initialdataRule];
stepn=0;
{timing,sol}=CheckAbort[FindRoot[alleqs,allvariablesValue,WorkingPrecision->workingprecise,AccuracyGoal->accuracyGoal,PrecisionGoal->preciseGoal,
EvaluationMonitor:>(stepn++;Print[{stepn,alleqs//Abs//Max}];If[stepn>maxStpes&&(alleqs//Abs//Max)> err4Abort,Abort[]])],"cannot find solution in some steps"]//AbsoluteTiming;
If[sol==="cannot find solution in some steps",Return["cannot find solution in some steps"]];
Print[timing];
If[!MatchQ[sol,{_Rule..}],Return["Wrong Happens"]];
alleqsp=D[totalActionExpression,{allvariables}];
checkEq={alleqs,alleqsp}/.Dispatch[sol];
checkEq=Max/@Abs/@checkEq;
actionValue=totalActionExpression/.Dispatch[sol];
Export[fileName<>".wl",{checkEq,actionValue,ImmirziValue,scaleDPhi,sol}];
sol
]
