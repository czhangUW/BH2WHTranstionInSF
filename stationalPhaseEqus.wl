(* ::Package:: *)

getSL2CRules[assignG0Rule_Association,assignG0DaggerRule_Association,myConjugateTransposeHead_,sl2cGaugeFixve_,su2GaugeFixve_]:=Block[{allve,sortTetraRule,sortTetraRule1,otherves,sl2cGaugeFixveRule,sl2cGaugeFixveRuleCon,su2GaugeFixveRule,su2GaugeFixveRuleCon,othervesRule,othervesRuleCon,sl2cRules,sl2cRulesCon,sl2cVariablesRule,Dg2DxyRules,Dg2DxyRulesCon},
allve=Keys[assignG0Rule];
otherves=DeleteCases[allve,_?(MemberQ[su2GaugeFixve,#]&)];
otherves=DeleteCases[otherves,_?(MemberQ[sl2cGaugeFixve,#]&)];
sl2cGaugeFixveRule=sl2cGaugeFixve->(sl2cGaugeFixve/.assignG0Rule)//Thread;
sl2cGaugeFixveRuleCon=(myConjugateTransposeHead@@@sl2cGaugeFixve)->(sl2cGaugeFixve/.assignG0DaggerRule)//Thread;
su2GaugeFixveRule=su2GaugeFixve/.assignG0Rule;
su2GaugeFixveRule=MapThread[Dot[#1,{{1+sl2cx1@@#2/Sqrt[2],(sl2cx2@@#2+I sl2cy2@@#2)/Sqrt[2]},{0,1/(1+sl2cx1@@#2/Sqrt[2])}}]&,{su2GaugeFixveRule,su2GaugeFixve}];
su2GaugeFixveRule= su2GaugeFixve->su2GaugeFixveRule//Thread;
su2GaugeFixveRuleCon=su2GaugeFixve/.assignG0DaggerRule;
su2GaugeFixveRuleCon=MapThread[Dot[{{1+sl2cx1@@#2/Sqrt[2],0},{(sl2cx2@@#2-I sl2cy2@@#2)/Sqrt[2],1/(1+sl2cx1@@#2/Sqrt[2])}},#1]&,{su2GaugeFixveRuleCon,su2GaugeFixve}];
su2GaugeFixveRuleCon=(myConjugateTransposeHead@@@su2GaugeFixve)->su2GaugeFixveRuleCon//Thread;
othervesRule=otherves/.assignG0Rule;
othervesRule=MapThread[Dot[#1,{{1+(sl2cx1@@#2+I sl2cy1@@#2)/Sqrt[2],(sl2cx2@@#2+I sl2cy2@@#2)/Sqrt[2]},{(sl2cx3@@#2+I sl2cy3@@#2)/Sqrt[2],(1+(sl2cx2@@#2+I sl2cy2@@#2)/Sqrt[2] (sl2cx3@@#2+I sl2cy3@@#2)/Sqrt[2])/(1+(sl2cx1@@#2+I sl2cy1@@#2)/Sqrt[2])}}]&,{othervesRule,otherves}];
othervesRule=otherves->othervesRule//Thread;
othervesRuleCon=otherves/.assignG0DaggerRule;
othervesRuleCon=MapThread[Dot[{{1+(sl2cx1@@#2-I sl2cy1@@#2)/Sqrt[2],(sl2cx3@@#2-I sl2cy3@@#2)/Sqrt[2]},{(sl2cx2@@#2-I sl2cy2@@#2)/Sqrt[2],(1+(sl2cx2@@#2-I sl2cy2@@#2)/Sqrt[2] (sl2cx3@@#2-I sl2cy3@@#2)/Sqrt[2])/(1+(sl2cx1@@#2-I sl2cy1@@#2)/Sqrt[2])}},#1]&,{othervesRuleCon,otherves}];
othervesRuleCon=(myConjugateTransposeHead@@@otherves)->othervesRuleCon//Thread;
sl2cRules={sl2cGaugeFixveRule,su2GaugeFixveRule,othervesRule}//Flatten;
sl2cRulesCon={sl2cGaugeFixveRuleCon,su2GaugeFixveRuleCon,othervesRuleCon}//Flatten;
sl2cVariablesRule={Map[{sl2cx1@@#1,sl2cy1@@#1,sl2cx2@@#1,sl2cy2@@#1,sl2cx3@@#1,sl2cy3@@#1}&,otherves]//Thread,
Map[{sl2cx1@@#1,sl2cx2@@#1,sl2cy2@@#1}&,su2GaugeFixve]//Thread}//Flatten;
{{sl2cRules,sl2cRulesCon}//Flatten//Dispatch,sl2cVariablesRule}
]


getSpinor0RuleFromSFData[orientatedTriangles_,assignValueRule_]:=Block[{allvef,zvfRule,sl2cve,sl2cveValue,checkEqualzve,zvfRulespinor,zvfRuleGaugaFix},
allvef=Function[u,Append[u,#[[1]]]]/@Most[#[[2]]]&/@orientatedTriangles//Flatten[#,1]&;
zvfRule=allvef/.assignValueRule;
zvfRule=(#[[1]].Transpose[#[[2,1]]]//Transpose//First)&/@zvfRule;
sl2cve=Most/@allvef;
sl2cveValue=sl2cve/.assignValueRule;
zvfRule=MapThread[Inverse[ConjugateTranspose[#1]].#2&,{sl2cveValue,zvfRule}];
zvfRule=If[#[[1]]!=0,#/(#[[1]]),#/#[[2]]]&/@zvfRule;
zvfRule=allvef->zvfRule//Thread;
zvfRule=GroupBy[zvfRule,Drop[Keys[#],{2}]&,Values];
checkEqualzve=AllTrue[zvfRule,#[[1]]-#[[2]]=={0,0}&];
If[!checkEqualzve,Print["may not get a consistent z_{vf}, the difference of the z_{vf} getting from Z_{vef} and Z_{ve'} is ", Map[Norm[#[[1]]-#[[2]]]&,((zvfRule[[#]]&/@Position[(#[[1]]-#[[2]]=={0,0})&/@zvfRule,False])),{2}]]];
zvfRule=If[#[[1,1]]!=0,{{1,#[[1,2]]},2},{{0,1},1}]&/@zvfRule;
zvfRule=zvfRule//Association;
zvfRulespinor=First/@zvfRule;
zvfRuleGaugaFix=Last/@zvfRule//Normal//Dispatch;
{zvfRulespinor,zvfRuleGaugaFix}
]
getSpinorRule[assignZ0Rule_Association,assignZ0DaggerRule_Association,gaugaFixRule_,myConjugateHead_]:=Block[{zvfRule,zvfRuleCon,spinorz,spinorvariables},
zvfRule=MapIndexed[Which[((#2[[1]]//First)/.gaugaFixRule)==2,#1+{0,spinorz@@(#2[[1]]//First)},((#2[[1]]//First)/.gaugaFixRule)==1,#1+{spinorz@@(#2[[1]]//First),0},((#2[[1]]//First)/.gaugaFixRule)!=1&&((#2[[1]]//First)/.gaugaFixRule)!=2,(Print["must choose a gauge for spinor"];Return[{}])]&,assignZ0Rule];
zvfRule=zvfRule/.spinorz[xx__]:>spinorx[xx]+I spinory[xx];
zvfRuleCon=MapIndexed[Which[((#2[[1]]//First)/.gaugaFixRule)==2,#1+{0,spinorz@@(#2[[1]]//First)},((#2[[1]]//First)/.gaugaFixRule)==1, #1+{spinorz@@(#2[[1]]//First),0},((#2[[1]]//First)/.gaugaFixRule)!=1&&((#2[[1]]//First)/.gaugaFixRule)!=2,(Print["must choose a gauge for spinor"];Return[{}])]&,assignZ0DaggerRule];
zvfRuleCon=zvfRuleCon/.spinorz[xx__]:>spinorx[xx]-I spinory[xx];
zvfRuleCon=KeyMap[myConjugateHead@@#&,zvfRuleCon];
spinorvariables=Keys[assignZ0Rule];
spinorvariables={spinorx@@#,spinory@@#}&/@spinorvariables;
spinorvariables=spinorvariables//Flatten;
{{zvfRule,zvfRuleCon}//Normal//Flatten//Dispatch,spinorvariables}
]


getAreaRule[orientatedTriangles_,assignValueRule_,ifbdyjdynamic_:False]:=Block[{allTrigs,area1,area2,areavariables},
allTrigs=Last/@(orientatedTriangles//Association);
area1=If[ifbdyjdynamic,MapIndexed[If[#1=="boundary",{areaj@@(#2//First),"boundary"},{areaj@@(#2//First),"internal"}]&,allTrigs],MapIndexed[If[#1=="boundary",{0,"boundary"},{areaj@@(#2//First),"internal"}]&,allTrigs]];
areavariables=GroupBy[area1//Values,Last,First/@#&];
area1=First/@area1;
area2=MapIndexed[((#2[[1]]//First)/.assignValueRule)&,allTrigs];
allTrigs=MapThread[(#1+1)#2&,{area1,area2}];
allTrigs=KeyMap[Area,allTrigs]//Dispatch;
{allTrigs,areavariables}
]



(*getAreaRule[orientatedTriangles_,assignValueRule_]:=Block[{allTrigs,area1,area2,areavariables},
allTrigs=Last/@(orientatedTriangles//Association);
area1=MapIndexed[If[#1=="boundary",0,areaj@@(#2//First)]&,allTrigs];
areavariables=DeleteCases[area1//Values,0];
area2=MapIndexed[((#2[[1]]//First)/.assignValueRule)&,allTrigs];
allTrigs=MapThread[#1+#2&,{area1,area2}];
allTrigs=KeyMap[Area,allTrigs]//Dispatch;
{allTrigs,areavariables}
]*)



actionTotal[orientatedTriangle_Rule,bdyspinors_,"spacelike",sl2cveRule_,zvfRule_,areafRule_]:=Block[{area,boundaryQ,boundary,Zvef,Zvef4Action,realpart,impart,myDotzz,myDotgz,myDot,action},
area=Area[orientatedTriangle[[1]]]/.areafRule;
Zvef=orientatedTriangle[[-1]]//Most;
boundaryQ=orientatedTriangle[[-1,-1]];
boundary=If[boundaryQ=="boundary",{Zvef[[1]]//Rest,Zvef[[-1]]//Rest},{}];
If[boundary!={},Zvef=Prepend[Zvef,boundary//First];Zvef=Append[Zvef,boundary//Last]];
Zvef=Append[#,orientatedTriangle[[1]]]&/@Zvef;
Zvef4Action=Partition[Zvef,2];
realpart=Log[(myDotzz[myConjugate@@#[[1]],#[[2]]])^2/((myDotzz[myConjugate@@#[[1]],#[[1]]]) (myDotzz[myConjugate@@#[[2]],#[[2]]]))]&/@Zvef4Action//Total;
impart=Log[myDotzz[myConjugate@@#[[1]],#[[1]]]/myDotzz[myConjugate@@#[[2]],#[[2]]] ]&/@Zvef4Action//Total;
action=realpart+(I Immirzi)impart;
action=action/.{Simplex[xx__],Tetrahedron[yy__],Triangle[zz__]}:>myDotgz[myConjugateTranspose[Simplex[xx],Tetrahedron[yy]],{Simplex[xx],Triangle[zz]}];
action=action/.myConjugate[Simplex[xx__],Tetrahedron[yy__],Triangle[zz__]]:>myDotgz[myConjugate[Simplex[xx],Triangle[zz]],{Simplex[xx],Tetrahedron[yy]}];
(*action=action/.myDotzz[myDotgz[zz_,yy_],myDotgz[xx_,uu_]]:>myDot[zz,yy,xx,uu];*)
action=action/.myDotzz[myDotgz[zz_,yy_],ww___]:>myDotzz[zz,yy,ww];
action=action/.myDotzz[ww___,myDotgz[zz_,yy_]]:>myDotzz[ww,zz,yy];
action=action/.myDotzz->myDot; 
action=action/.sl2cveRule;
action=action/.zvfRule;
action=action/.myConjugate[xx_Tetrahedron,yy_Triangle]:>Conjugate[(#[[1]].Transpose[#[[2,1]]]//Transpose//First)&[({xx,yy}/.bdyspinors)]];
action=action/.{xx_Tetrahedron,yy_Triangle}:>((#[[1]].Transpose[#[[2,1]]]//Transpose//First)&[({xx,yy}/.bdyspinors)]);
action=area action/.myDot->Dot
]

actionTotal[orientatedTriangle:{_Rule..},bdyspinors_,"spacelike",sl2cveRule_,zvfRule_,areafRule_,bdyStatephase_:0]:=Block[{eachTerm},
eachTerm=actionTotal[#,bdyspinors,"spacelike",sl2cveRule,zvfRule,areafRule]&/@orientatedTriangle;
(eachTerm//Total)+bdyStatephase
]



(*getbdyCoherentStatePhase[orientatedTriangle:{_Rule..},area0Rule_,gaussPhi0Rule_,gaussSpreadRule_]:=Block[{bdyTrig,darea,sqrtarea,dareaBySqrtArea,phi0,gaussSpreadSymbol,gaussSpread,coherenStatephase},
bdyTrig=Cases[orientatedTriangle,HoldPattern[_->{__,"boundary"}]];
bdyTrig=Keys[bdyTrig];
darea=(areaj/@bdyTrig);
sqrtarea=Area/@bdyTrig/.area0Rule;
sqrtarea=Sqrt[sqrtarea];
dareaBySqrtArea=darea/sqrtarea;
phi0=bdyTrig/.gaussPhi0Rule;
gaussSpreadSymbol=Table[{bdyTrig[[a]],bdyTrig[[b]]},{a,1,Length[bdyTrig]},{b,1,Length[bdyTrig]}];
gaussSpread=gaussSpreadSymbol/.gaussSpreadRule;
coherenStatephase=I phi0.darea-1/2 dareaBySqrtArea.gaussSpread.dareaBySqrtArea
]*)
getbdyCoherentStatePhase[orientatedTriangle:{_Rule..},areafRule_,gaussPhi0Rule_,gaussSpreadRule_]:=
Block[{bdyTrig,darea,area0,phi0,gaussSpreadSymbol,gaussSpread,coherenStatephase},
bdyTrig=Cases[orientatedTriangle,HoldPattern[_->{__,"boundary"}]];
bdyTrig=Keys[bdyTrig];
darea=(Area/@bdyTrig);
darea=darea/.areafRule;
area0=darea/.Subscript[areaj,_]:>0;
darea=darea-area0;
phi0=bdyTrig/.gaussPhi0Rule;
gaussSpreadSymbol=Table[{bdyTrig[[a]],bdyTrig[[b]]},{a,1,Length[bdyTrig]},{b,1,Length[bdyTrig]}];
gaussSpread=gaussSpreadSymbol/.gaussSpreadRule;
coherenStatephase=I phi0.darea-1/2 darea.gaussSpread.darea
]


(*note that phi0 in the coherent state is defined by d_jS_{SF}+i phi0=0 so that phi0=i d_jS_{SF}*)
getFlatCoherentPhi0[allOrientatedTriangle:{_Rule..},bdyspinors_,"spacelike",sl2cveRule_,zvfRule_,vanishingVariableRule_]:=Block[{bdyTrig,djaction},
bdyTrig=Cases[allOrientatedTriangle,HoldPattern[_->{__,"boundary"}]];
djaction=actionTotal[#,bdyspinors,"spacelike",sl2cveRule,zvfRule,Area[__]:>1]&/@bdyTrig;
djaction=djaction/.vanishingVariableRule;
djaction=I djaction;
bdyTrig=Keys[bdyTrig];
Rule[bdyTrig,djaction]//Thread//Association
]
getCoherentSpread[allOrientatedTriangle:{_Rule..},spreaValueFun_]:=Block[{bdyTrig,spreaValue},
bdyTrig=Cases[allOrientatedTriangle,HoldPattern[_->{__,"boundary"}]];
bdyTrig=Keys[bdyTrig];
bdyTrig=Tuples[bdyTrig,2];
spreaValue=spreaValueFun/@bdyTrig;
Rule[bdyTrig,spreaValue]//Thread//Dispatch
]


(*getbdyEqus[orientatedTriangle_,bdyspinors_,sl2cveRule_,zvfRule_,areafRule_,vanishingVariableRule_,gaussSpread_:1]:=Block[{Zvef,boundary,Zvef4Action,myDotzz,myDotgz,myDot,realpart,impart,action,actionValue0,darea,area0},
Zvef=orientatedTriangle[[-1]]//Most;
boundary={Zvef[[1]]//Rest,Zvef[[-1]]//Rest};
Zvef=Prepend[Zvef,boundary//First];
Zvef=Append[Zvef,boundary//Last];
Zvef=Append[#,orientatedTriangle[[1]]]&/@Zvef;
Zvef4Action=Partition[Zvef,2];
realpart=Log[(myDotzz[myConjugate@@#[[1]],#[[2]]])^2/((myDotzz[myConjugate@@#[[1]],#[[1]]]) (myDotzz[myConjugate@@#[[2]],#[[2]]]))]&/@Zvef4Action//Total;
impart=Log[myDotzz[myConjugate@@#[[1]],#[[1]]]/myDotzz[myConjugate@@#[[2]],#[[2]]] ]&/@Zvef4Action//Total;
action=realpart+(I Immirzi)impart;
action=action/.{Simplex[xx__],Tetrahedron[yy__],Triangle[zz__]}:>myDotgz[myConjugateTranspose[Simplex[xx],Tetrahedron[yy]],{Simplex[xx],Triangle[zz]}];
action=action/.myConjugate[Simplex[xx__],Tetrahedron[yy__],Triangle[zz__]]:>myDotgz[myConjugate[Simplex[xx],Triangle[zz]],{Simplex[xx],Tetrahedron[yy]}];
action=action/.myDotzz[myDotgz[zz_,yy_],ww___]:>myDotzz[zz,yy,ww];
action=action/.myDotzz[ww___,myDotgz[zz_,yy_]]:>myDotzz[ww,zz,yy];
action=action/.myDotzz->myDot;
action=action/.sl2cveRule;
action=action/.zvfRule;
action=action/.myConjugate[xx_Tetrahedron,yy_Triangle]:>Conjugate[(#[[1]].Transpose[#[[2,1]]]//Transpose//First)&[({xx,yy}/.bdyspinors)]];
action=action/.{xx_Tetrahedron,yy_Triangle}:>((#[[1]].Transpose[#[[2,1]]]//Transpose//First)&[({xx,yy}/.bdyspinors)]);
action=action/.myDot->Dot;
actionValue0=action/.vanishingVariableRule;
area0=Area[orientatedTriangle[[1]]]/.areafRule;
area0=area0/.vanishingVariableRule;
darea=areaj[orientatedTriangle[[1]]];
action-2gaussSpread darea/Sqrt[area0]-actionValue0
]*)
