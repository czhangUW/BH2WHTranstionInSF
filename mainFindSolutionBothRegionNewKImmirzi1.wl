(* ::Package:: *)

Get["forTriangulation.wl"]
Get["fromGeometryToSFData.wl"]
Get["solveBdyData.wl"]
Get["fromGeometryToSFDataCurved.wl"]
Get["stationalPhaseEqus.wl"]
Get["getComplexCritical.wl"]
Get["getComplexCriticalBothRegion.wl"]
Protect[{V,t,x,y,z,\[Delta]L,Vp,myConjugateTranspose,myConjugate,p}];
SetAttributes[{t,x,y,z,V,Vp,\[Delta]L,myConjugateTranspose,myConjugate,p},NHoldAll];
eta={-1,1,1,1}//DiagonalMatrix;
sigma4=PauliMatrix/@Range[0,3];
epsilon=LeviCivitaTensor[4]//Normal;
tildesigma4={-PauliMatrix[0],PauliMatrix[1],PauliMatrix[2],PauliMatrix[3]};
rule4Bp={V[5]->V[p[5]],V[6]->V[p[6]],V[7]->V[p[7]],V[8]->V[p[8]]};
precise=200;
preciseND=50;
chopdelta=20;
M=2000;
immiriziValue=1/(Sqrt[2] 3^(1/4));
alphaValue=1;
f[r_]:=1-(2M)/r+alphaValue M^2/r^4
beta[theta_,r0_]:=Sqrt[1-2/(f[r0](1+Cosh[theta]))]
rangleTheta[r_]:={ArcCosh[2/f[r]-1],ArcCosh[2/((1-(1/3)^2)f[r])-1]}//Chop
rb=(alphaValue M/2)^(1/3);


(* ::Section:: *)
(*Triangulation of the spacetime region B_m*)


vTetra1=V/@Range[4];
vTetra2=V/@Range[5,8];
vTetra2p=V/@Range[9,12];
vertexLabel4Triangulation=Tuples[{Subsets[{1,2,3,4},{#}],Subsets[{1,2,3,4},{4-#}]}]&/@{1,2,3}//Flatten[#,1]&;
vertexLabel4Triangulation=vertexLabel4Triangulation//DeleteCases[#,_?(IntersectingQ@@#&)]&;
pastTetrahedra={vTetra1[[#[[1]]]],vTetra2[[#[[2]]]]}&/@vertexLabel4Triangulation;
pastTetrahedra=Flatten[#,1]&/@pastTetrahedra;
{simplicesInLabel,bdyTetrahedra}=simpliciesAndTheirBdy[pastTetrahedra,{vTetra2,vTetra2p}];
simplicesInLabel=Sort/@simplicesInLabel;
allTetrahedra=Subsets[#,{4}]&/@simplicesInLabel;
allTetrahedra=Flatten[allTetrahedra,1];
allTetrahedra=Sort/@allTetrahedra//DeleteDuplicates;
allTriangles=Subsets[#,{3}]&/@allTetrahedra;
allTriangles=Flatten[allTriangles,1];
allTriangles=Sort/@allTriangles//DeleteDuplicates;
bdyTetrahedra=Map[Sort,bdyTetrahedra,{2}];
bdyTetrahedrap=bdyTetrahedra//Flatten[#,1]&;
internalTetra=DeleteCases[allTetrahedra,_?(MemberQ[bdyTetrahedrap,#]&)];
allEdges=Map[Subsets[#,{2}]&,bdyTetrahedra,{2}];
allEdges=Flatten[#,1]&/@allEdges;
allEdges=Map[Sort,allEdges,{2}];
allEdges=DeleteDuplicates/@allEdges;
futureEdges=allEdges[[2]];
allEdges=Flatten[allEdges,1];
futureEdges=DeleteCases[futureEdges,_?(Length[Cases[allEdges, #]]==2&)];


(* ::Section:: *)
(*Determine Parameter*)


r1=rb//N[#,precise]&;
r2=(2M+1/100 M)//N[#,precise]&;
r3=(2M+1/10 M)//N[#,precise]&;
rangleTheta1={ArcCosh[2/f[r1]-1],ArcCosh[2/f[r1] (1-((r2-3r1)/(3(r2-r1)))^2)^-1-1]}//Chop[#,10^-chopdelta]&;
rangleTheta3={ArcCosh[2/f[r3] (1-((r2-r1)/(3(r3-r1)))^2)^-1-1],ArcCosh[9/(4f[r3])-1]};
\[Theta]1=(rangleTheta1//Last)-10^-4;
\[Theta]3=(rangleTheta3//Last)-10^-4;
ep=-1/(r3-3r1) ((r2-r1)Sqrt[1-2/((Cosh[\[Theta]1]+1)f[r1])]+(r3-r1)Sqrt[1-2/((Cosh[\[Theta]3]+1)f[r3])]-(r2+r3-4r1)/3);
delta=-1/(r3-3r1) ((r2-r1)Sqrt[1-2/((Cosh[\[Theta]1]+1)f[r1])]-(r2-3r1)/3);
t3=(1/3-ep)(r3-3 r1);
t2=1/3 (r2-3r1)-delta(r3-3r1);
vertexCoor1=r1 {{Sqrt[8/9],0,-1/3},{-Sqrt[2/9],Sqrt[2/3],-1/3},{-Sqrt[2/9],-Sqrt[2/3],-1/3},{0,0,1}};
vertexCoor2=-r2 vertexCoor1/r1;
vertexCoor3=-r3 vertexCoor1/r1;
vertexCoor1=Prepend[#,0]&/@vertexCoor1;
vertexCoor2=Prepend[#,t2]&/@vertexCoor2;
vertexCoor3=Prepend[#,t3]&/@vertexCoor3;
ruleLabelVertex=Rule[{vTetra1,vTetra2,vTetra2p},{vertexCoor1,vertexCoor2,vertexCoor3}]//Thread;
ruleLabelVertex=Thread/@ruleLabelVertex//Flatten;


(* ::Section:: *)
(*Check Parameter*)


twoComplex=getSFDataFromFlatComplex[ruleLabelVertex,simplicesInLabel,bdyTetrahedrap][[4]];
internalFaces=Cases[twoComplex,HoldPattern[_->{__,"internal"}]]//Association;
internalFaces=Most/@internalFaces;
internalFaces=Rule@@@#&/@internalFaces;
internalFaces=Normal/@(GroupBy[#,Keys,Values]&/@internalFaces);
dihedralInterface=dihedralAngleInFlatGeometry[#,ruleLabelVertex]&/@internalFaces//N;
Select[dihedralInterface,#!=0&]


allspacelikeQ=AllTrue[Sign[#.eta.#]&/@(getTetrahedronNormal/@(allTetrahedra/.ruleLabelVertex)),#==-1&];
Print["Are all tetrahedra spacelike?----->",allspacelikeQ]


(* ::Subsection:: *)
(*Get boundary dihedral angel*)


bdyOfBRegion=Drop[bdyTetrahedra,{2}]//Flatten[#,1]&;
sharedTrigsOfBRegion=(Tetrahedron@@#)->(Triangle@@@Subsets[#,{3}])&/@bdyOfBRegion;
sharedTrigsOfBRegion=Thread/@sharedTrigsOfBRegion//Flatten;
sharedTrigsOfBRegion=GroupBy[sharedTrigsOfBRegion,Values,Keys];
otherTrigsofBregion=Select[sharedTrigsOfBRegion,Length[#]==1&];
sharedTrigsOfBRegion=Select[sharedTrigsOfBRegion,Length[#]==2&];


SFDataFlat0=getSFDataFromFlatComplex[ruleLabelVertex,simplicesInLabel,bdyTetrahedrap];
sharedTrigInSimplex=#->#&/@Keys[sharedTrigsOfBRegion]//Association;
sharedTrigInSimplex=#/.SFDataFlat0[[4]]&/@sharedTrigInSimplex;
sharedTrigInSimplex=Most/@sharedTrigInSimplex;
tetrahedronInSimplex=GroupBy[#,First,(Transpose[#]//Last)&]&/@sharedTrigInSimplex;
tetrahedronInSimplex=Normal/@tetrahedronInSimplex;
flatDihedral=dihedralAngleInFlatGeometry[#,ruleLabelVertex]&/@tetrahedronInSimplex//Normal;


gatherTrigByDihedral=GroupBy[flatDihedral,SetPrecision[#//Values,10]&,Keys];
gatherTrigByDihedral=First[#]->#&/@gatherTrigByDihedral//Values;
representTrigs=Keys[gatherTrigByDihedral];
representTrigs=representTrigs->representTrigs//Thread//Association;
representingInTetra=sharedTrigsOfBRegion[#]&/@representTrigs;


Function[u,beta[u]=Block[{deciderth},deciderth=FirstCase[List@@u,_?(MemberQ[{vTetra1,vTetra2p}//Flatten,#]&)];
deciderth=If[MemberQ[vTetra1,deciderth],{\[Theta]1,r1},{\[Theta]3,r3}];beta@@deciderth
]
]/@(representingInTetra//Values//Flatten);


If[FileExistsQ["./results/dihedralFromCurvedGeo.wl"],dihedralFromCurvedGeo=Import["./results/dihedralFromCurvedGeo.wl"];,
representingDihedralFromCurvedGeo=MapIndexed[intKAlongLink[{Function[{x,y,z},extrinsicKFun[x,y,z,beta[#1//First]]],Function[{x,y,z},extrinsicKFun[x,y,z,beta[#1//Last]]]},
{Function[{x,y,z},metricFun[x,y,z,beta[#1//First]]],Function[{x,y,z},metricFun[x,y,z,beta[#1//Last]]]},Map[Rest,((List@@@#1)/.ruleLabelVertex),{2}],
Map[Rest,(List@@(#2//First//First))/.ruleLabelVertex]]&,representingInTetra]//SetPrecision[#,precise]&;
dihedralFromCurvedGeo=Reverse/@(Thread/@gatherTrigByDihedral//Flatten)//Association;
dihedralFromCurvedGeo=(#/.representingDihedralFromCurvedGeo)&/@dihedralFromCurvedGeo;
Export["./results/dihedralFromCurvedGeo.wl",dihedralFromCurvedGeo];
]


(* ::Section:: *)
(*Real critical point matching Boundary Data*)


ruleLabelVertexCurvedGeometryp=curvedCoors[#,futureEdges,ruleLabelVertex]&/@simplicesInLabel;
ruleLabelVertexCurvedGeometry0=ruleLabelVertexCurvedGeometryp/.\[Delta]L[1]->0;
curvedSFData0=getSFDataFromCurvedComplex[ruleLabelVertexCurvedGeometry0,simplicesInLabel,bdyTetrahedrap];


Unprotect[{sl2cx1,sl2cx2,sl2cx3,sl2cy1,sl2cy2,sl2cy3,spinorx,spinory,areaj}];
Clear[sl2cx1,sl2cx2,sl2cx3,sl2cy1,sl2cy2,sl2cy3,spinorx,spinory,areaj]
allTrigs=Function[u,Append[u,#[[1]]]]/@Most[#[[2]]]&/@curvedSFData0[[4]]//Flatten[#,1]&;
forAreas=Last/@allTrigs//DeleteDuplicates;
MapIndexed[Set[areaj[#1],Subscript[areaj, #2//First]]&,forAreas];
forAreas=forAreas/.rule4Bp//DeleteCases[#,Triangle[V[_Integer]..]]&;
correspondenceBmp=Apply[Sequence,#1,{2}]&/@forAreas;
MapThread[Set[areaj[#1],Subscript[areaj,areaj[#2]//Last//p]] &,{forAreas,correspondenceBmp}];
allve=Most/@allTrigs//DeleteDuplicates;
MapIndexed[{Set@@{sl2cx1@@#1,Subscript[sl2cx1, #2//First]},Set@@{sl2cy1@@#1,Subscript[sl2cy1, #2//First]},Set@@{sl2cx2@@#1,Subscript[sl2cx2, #2//First]},Set@@{sl2cy2@@#1,Subscript[sl2cy2, #2//First]},Set@@{sl2cx3@@#1,Subscript[sl2cx3, #2//First]},Set@@{sl2cy3@@#1,Subscript[sl2cy3, #2//First]}}&,allve]//Flatten;
allve=allve/.rule4Bp//DeleteCases[#,{Simplex[V[_Integer]..],Tetrahedron[V[_Integer]..]}]&;
correspondenceBmp=Apply[Sequence,#1,{3}]&/@allve;
MapThread[{Set@@{sl2cx1@@#1,Subscript[sl2cx1, sl2cx1@@#2//Last//p]},Set@@{sl2cy1@@#1,Subscript[sl2cy1, sl2cy1@@#2//Last//p]},Set@@{sl2cx2@@#1,Subscript[sl2cx2, sl2cx2@@#2//Last//p]},Set@@{sl2cy2@@#1,Subscript[sl2cy2, sl2cy2@@#2//Last//p]},Set@@{sl2cx3@@#1,Subscript[sl2cx3, sl2cx3@@#2//Last//p]},Set@@{sl2cy3@@#1,Subscript[sl2cy3, sl2cy3@@#2//Last//p]}}&,{allve,correspondenceBmp}]//Flatten;
allvf=Drop[#,{2}]&/@allTrigs//DeleteDuplicates;
MapIndexed[{Set@@{spinorx@@#1,Subscript[spinorx, #2//First]},Set@@{spinory@@#1,Subscript[spinory, #2//First]}}&,allvf]//Flatten;
allvf=allvf/.rule4Bp//DeleteCases[#,{Simplex[V[_Integer]..],Triangle[V[_Integer]..]}]&;
correspondenceBmp=Apply[Sequence,#1,{3}]&/@allvf;
MapThread[{Set@@{spinorx@@#1,Subscript[spinorx, spinorx@@#2//Last//p]},Set@@{spinory@@#1,Subscript[spinory, spinory@@#2//Last//p]}}&,{allvf,correspondenceBmp}]//Flatten;
Protect[{sl2cx1,sl2cx2,sl2cx3,sl2cy1,sl2cy2,sl2cy3,spinorx,spinory,areaj}];
SetAttributes[{sl2cx1,sl2cx2,sl2cx3,sl2cy1,sl2cy2,sl2cy3,spinorx,spinory,areaj},NHoldAll];


allTetrahedraInSimplex=(simplicesInLabel->(Sort[Subsets[#,{4}]]&/@simplicesInLabel))//Thread//Association;
allTetrahedraInSimplex=Apply[Tetrahedron,allTetrahedraInSimplex,{2}];
allTetrahedraInSimplex=KeyMap[Simplex@@#&,allTetrahedraInSimplex];
sortFutureSideBdyTetra=Map[Sort,bdyTetrahedra,{2}];
sortFutureSideBdyTetra=Rule[Apply[Tetrahedron,sortFutureSideBdyTetra,{2}],{0,2,0}]//Thread;
sortFutureSideBdyTetra=Thread/@sortFutureSideBdyTetra;
sortFutureSideBdyTetra=sortFutureSideBdyTetra//Flatten;
prioriSL2CGaugeFix=Cases[#,_?((#/.sortFutureSideBdyTetra)==0&)]&/@allTetrahedraInSimplex;
prioriSL2CGaugeFix=DeleteCases[prioriSL2CGaugeFix,{}];
prioriSL2CGaugeFix=Thread/@Normal[prioriSL2CGaugeFix]//Flatten;
prioriSL2CGaugeFix=List@@@prioriSL2CGaugeFix;
forbidenve=Cases[#,_?((#/.sortFutureSideBdyTetra)==2&)]&/@allTetrahedraInSimplex;
forbidenve=DeleteCases[forbidenve,{}];
forbidenve=Thread/@Normal[forbidenve]//Flatten;
forbidenve=List@@@forbidenve;
sl2cGaugeFixTetr=NestWhile[fixSL2CGauge,{allTetrahedraInSimplex,Keys[allTetrahedraInSimplex],{},forbidenve,prioriSL2CGaugeFix},#[[2]]=!={}&][[3]];
su2GaugeFixve=allTetrahedraInSimplex//Normal;
su2GaugeFixve=Thread/@su2GaugeFixve//Flatten;
su2GaugeFixve=List@@@su2GaugeFixve;
su2GaugeFixve=GroupBy[su2GaugeFixve,Last];
su2GaugeFixve=Select[su2GaugeFixve,Length[#]==2&]//Values;
su2GaugeFixve=DeleteCases[#,_?(MemberQ[sl2cGaugeFixTetr,#]&)]&/@su2GaugeFixve;
su2GaugeFixve=First/@su2GaugeFixve;
assignG0Rule=Cases[curvedSFData0[[1]]//Normal,HoldPattern[{_Simplex,_Tetrahedron}->_]]//Association;
assignG0DaggerRule=ConjugateTranspose/@assignG0Rule;
{sl2cRules4CC,sl2cVariables}=getSL2CRules[assignG0Rule,assignG0DaggerRule,myConjugateTranspose,sl2cGaugeFixTetr,su2GaugeFixve];
{assignZ0Rule,assignZ0GaugeRule}=getSpinor0RuleFromSFData[curvedSFData0[[4]],curvedSFData0[[1]]];
assignZ0DaggerRule=Conjugate/@assignZ0Rule;
{spinorRules4CC,spinorVariables}=getSpinorRule[assignZ0Rule,assignZ0DaggerRule,assignZ0GaugeRule,myConjugate];
{areafRule,areaVariables}=getAreaRule[curvedSFData0[[4]],curvedSFData0[[2]],True];
bdyTrigs=Cases[curvedSFData0[[4]],HoldPattern[_->{__,"boundary"}]];
actionAtBdyf=actionTotal[#,curvedSFData0[[3]],"spacelike",sl2cRules4CC,spinorRules4CC,areafRule]&/@bdyTrigs;
areaInvolvedInEq=Cases[#,Subscript[areaj,_],2]&/@actionAtBdyf//Flatten;
allvariablesValues={areaVariables["internal"],sl2cVariables,spinorVariables,areaVariables["boundary"]}//Flatten;
allvariablesValues=#->0&/@allvariablesValues//Dispatch;
actionAtBdyf=MapThread[Keys[#1]->D[#2,#3]&,{bdyTrigs,actionAtBdyf,areaInvolvedInEq}]/.allvariablesValues//Association;
dihedralPartOfAction=I #&/@actionAtBdyf; (*Here we get phi0 in the coherent state, which is defined by d_jS_{SF}+i phi0=0 so that phi0=i d_jS_{SF}.*)
dihedralPartOfAction=Chop[Coefficient[#,Immirzi],10^-chopdelta]&/@dihedralPartOfAction;
dihedralPartOfAction=-dihedralPartOfAction;(*Since by our definition phi=(twist angle) - Immirzi (dihedral angle). *)
dihedralCompare=Merge[{dihedralFromCurvedGeo,dihedralPartOfAction},Identity];
dihedralCompare=Select[dihedralCompare,Length[#]==2&];
dihedralCompare=Abs[Sign[#[[1]]]-Sign[#[[2]]]]&/@dihedralCompare;
dihedralCompare=Select[dihedralCompare,#==2&]//Keys;
parityTransedVertices=dihedralCompare/.curvedSFData0[[4]];
parityTransedVertices=Cases[Flatten[parityTransedVertices],_Simplex]//DeleteDuplicates;
parityTransedSFData=curvedSFData0[[1]]//Normal;
parityTransedSFData=Which[Length[parityTransedVertices]==Length[simplicesInLabel],parityTransedSFData/.({ss_Simplex,tt_Tetrahedron}->zz_):>({ss,tt}->Inverse[Conjugate[Transpose[zz]]]),Length[parityTransedVertices]==0,parityTransedSFData,Length[parityTransedVertices]!=0&&Length[parityTransedVertices]!=Length[parityTransedVertices],Print["the flat geometry didn't match the extrinsic curvature well"]
];
parityTransedSFData=parityTransedSFData//Dispatch;
curvedSFData0=ReplacePart[curvedSFData0,1->Dispatch[parityTransedSFData]];


(* ::Section:: *)
(*Complex Critical Point*)


allTetrahedraInSimplex=(simplicesInLabel->(Sort[Subsets[#,{4}]]&/@simplicesInLabel))//Thread//Association;
allTetrahedraInSimplex=Apply[Tetrahedron,allTetrahedraInSimplex,{2}];
allTetrahedraInSimplex=KeyMap[Simplex@@#&,allTetrahedraInSimplex];
sortFutureSideBdyTetra=Map[Sort,bdyTetrahedra,{2}];
sortFutureSideBdyTetra=Rule[Apply[Tetrahedron,sortFutureSideBdyTetra,{2}],{0,2,0}]//Thread;
sortFutureSideBdyTetra=Thread/@sortFutureSideBdyTetra;
sortFutureSideBdyTetra=sortFutureSideBdyTetra//Flatten;
prioriSL2CGaugeFix=Cases[#,_?((#/.sortFutureSideBdyTetra)==0&)]&/@allTetrahedraInSimplex;
prioriSL2CGaugeFix=DeleteCases[prioriSL2CGaugeFix,{}];
prioriSL2CGaugeFix=Thread/@Normal[prioriSL2CGaugeFix]//Flatten;
prioriSL2CGaugeFix=List@@@prioriSL2CGaugeFix;
forbidenve=Cases[#,_?((#/.sortFutureSideBdyTetra)==2&)]&/@allTetrahedraInSimplex;
forbidenve=DeleteCases[forbidenve,{}];
forbidenve=Thread/@Normal[forbidenve]//Flatten;
forbidenve=List@@@forbidenve;
sl2cGaugeFixTetr=NestWhile[fixSL2CGauge,{allTetrahedraInSimplex,Keys[allTetrahedraInSimplex],{},forbidenve,prioriSL2CGaugeFix},#[[2]]=!={}&][[3]];
su2GaugeFixve=allTetrahedraInSimplex//Normal;
su2GaugeFixve=Thread/@su2GaugeFixve//Flatten;
su2GaugeFixve=List@@@su2GaugeFixve;
su2GaugeFixve=GroupBy[su2GaugeFixve,Last];
su2GaugeFixve=Select[su2GaugeFixve,Length[#]==2&]//Values;
su2GaugeFixve=DeleteCases[#,_?(MemberQ[sl2cGaugeFixTetr,#]&)]&/@su2GaugeFixve;
su2GaugeFixve=First/@su2GaugeFixve;
sl2cGaugeFixTetr={sl2cGaugeFixTetr,sl2cGaugeFixTetr/.rule4Bp}//Flatten[#,1]&//DeleteDuplicates;
su2GaugeFixveBp=Join[su2GaugeFixve,forbidenve]/.rule4Bp;
su2GaugeFixve=Join[su2GaugeFixve,su2GaugeFixveBp]//DeleteDuplicates;


curvedSFDataBm=curvedSFData0;
futureTetrahedra=Sort/@bdyTetrahedra[[2]];
futureTetrahedra=Tetrahedron@@@futureTetrahedra;
curvedSFData=sfDataFromBmToBmp[curvedSFDataBm,rule4Bp,futureTetrahedra];
assignG0RuleBm=Cases[curvedSFDataBm[[1]]//Normal,HoldPattern[{_Simplex,_Tetrahedron}->_]]//Association;
assignG0DaggerRuleBm=ConjugateTranspose/@assignG0RuleBm;
assignG0RuleBp=assignG0RuleBm;
assignG0RuleBp=KeyMap[#/.rule4Bp&,assignG0RuleBp];
assignG0DaggerRuleBp=assignG0DaggerRuleBm;
assignG0DaggerRuleBp=KeyMap[#/.rule4Bp&,assignG0DaggerRuleBp];
assignG0Rule=Join[assignG0RuleBm,assignG0RuleBp]//SetPrecision[#,precise]&;
assignG0DaggerRule=Join[assignG0DaggerRuleBm,assignG0DaggerRuleBp]//SetPrecision[#,precise]&;
{sl2cRules4CC,sl2cVariables}=getSL2CRules[assignG0Rule,assignG0DaggerRule,myConjugateTranspose,sl2cGaugeFixTetr,su2GaugeFixve];


{assignZ0RuleBm,assignZ0GaugeRuleBm}=getSpinor0RuleFromSFData[curvedSFDataBm[[4]],curvedSFDataBm[[1]]];
assignZ0DaggerRuleBm=Conjugate/@assignZ0RuleBm;
assignZ0RuleBp=assignZ0RuleBm;
assignZ0RuleBp=KeyMap[#/.rule4Bp&,assignZ0RuleBp];
assignZ0DaggerRuleBp=assignZ0DaggerRuleBm;
assignZ0DaggerRuleBp=KeyMap[#/.rule4Bp&,assignZ0DaggerRuleBp];
assignZ0Rule=Join[assignZ0RuleBm,assignZ0RuleBp]//SetPrecision[#,precise]&;
assignZ0DaggerRule=Join[assignZ0DaggerRuleBm,assignZ0DaggerRuleBp]//SetPrecision[#,precise]&;
assignZ0GaugeRuleBm=assignZ0GaugeRuleBm//Normal;
assignZ0GaugeFixRuleBp=assignZ0GaugeRuleBm/.rule4Bp;
assignZ0GaugeFixRule={assignZ0GaugeRuleBm,assignZ0GaugeFixRuleBp}//Flatten//Dispatch;
{spinorRules4CC,spinorVariables}=getSpinorRule[assignZ0Rule,assignZ0DaggerRule,assignZ0GaugeFixRule,myConjugate];


areafRuleBm=curvedSFDataBm[[2]];
areafRuleBm=Normal[areafRuleBm]//Association;
areafRuleBp=areafRuleBm;
areafRuleBp=KeyMap[(#/.rule4Bp)&,areafRuleBp];
areafRule=Join[areafRuleBm,areafRuleBp]//Normal//SetPrecision[#,precise]&//Dispatch;
{areafRule,areaVariables}=getAreaRule[curvedSFData[[4]],areafRule,True];


Export["./results/parameters.wl",{M,rb,areafRule}]


allvariables={areaVariables["internal"],sl2cVariables,spinorVariables,areaVariables["boundary"]}//Flatten;
allvariablesp=allvariablesp={{areaVariables["internal"],areaVariables["boundary"]}//Flatten,{sl2cVariables,spinorVariables}//Flatten};


checkSignIntKPho0[curvedSFData,sl2cRules4CC,spinorRules4CC,allvariables,rule4Bp,dihedralFromCurvedGeo]


checkFlateEquation=findSolutions[curvedSFData,sl2cRules4CC,spinorRules4CC,areafRule,allvariablesp,rule4Bp,dihedralFromCurvedGeo,1,{},immiriziValue,"whatever",True];
Print["Is it correcct that the eoms are only not satisfied for boundary faces?----->",SubsetQ[areaVariables["boundary"],checkFlateEquation]]


scaleDphi0=10^-4;
If[!FileExistsQ["./results/solutionNewK0.wl"],findSolutions[curvedSFData,sl2cRules4CC,spinorRules4CC,areafRule,allvariablesp,rule4Bp,dihedralFromCurvedGeo,scaleDphi0,{},immiriziValue,"./results/solutionNewK0"]
];
initial0=Import["./results/solutionNewK0.wl"][[-1]];


scaleDphi=10^(Range[-3,-2,1]);


notCalculate=scaleDphi->(FileExistsQ["./results/solutionNewK0"<>ToString[#]<>".wl"]&/@Range[Length[scaleDphi]])//Thread//Association;
whichToCalculate=DeleteCases[notCalculate,True]//Keys;
nNotCalculate=Length[whichToCalculate];


If[nNotCalculate!=0,
pos=Position[scaleDphi,#]&/@whichToCalculate//Flatten;
fileName="./results/solutionNewK0"<>ToString[#]&/@pos;
Do[otherInitial[i]=(whichToCalculate[[i]]/scaleDphi0)#&/@Association[initial0],{i,1,Length[whichToCalculate]}];
LaunchKernels[Length[whichToCalculate]];
Print["we will calculate the result for scaleDphi=",whichToCalculate," by the scaled equations, with initial data in ",otherInitial[1][[1]]," ... ", otherInitial[Length[scaleDphi]][[1]]];
ParallelDo[({timing,solList[i]}=findSolutions[curvedSFData,sl2cRules4CC,spinorRules4CC,areafRule,allvariablesp,rule4Bp,dihedralFromCurvedGeo,scaleDphi[[i]],
otherInitial[i]//Normal,immiriziValue,fileName[[i]]]//AbsoluteTiming;Print[timing]),{i,1,Length[whichToCalculate]}]
]


initial0=Import["./results/solutionNewK0"<>ToString[Length[scaleDphi]]<>".wl"][[-1]];


scaleDphi=Range[1/100,1,1/500]//Rest;


numberOfCalculation=20;
nNotCalculate=Length[scaleDphi];
While[nNotCalculate!=0,
whichToCalculate=scaleDphi->(FileExistsQ["./results/solutionNewK"<>ToString[#]<>".wl"]&/@Range[Length[scaleDphi]])//Thread//Association;
whichToCalculate=DeleteCases[whichToCalculate,True]//Keys;
nNotCalculate=Length[whichToCalculate];
If[nNotCalculate!=0,
toBeCalculated=If[Length[whichToCalculate]>=numberOfCalculation,whichToCalculate[[1;;numberOfCalculation]],whichToCalculate];
pos=Position[scaleDphi,#]&/@toBeCalculated//Flatten;
fileName="./results/solutionNewK"<>ToString[#]&/@pos;
initial=initial0;
initialI=1;
While[FileExistsQ["./results/solutionNewK"<>ToString[initialI]<>".wl"],
initial=Import["./results/solutionNewK"<>ToString[initialI]<>".wl"][[-1]];initialI++];
Print["we will calculate the result for scaleDphi=",toBeCalculated," by the scaled equations, with initial data in ",If[initial==={},{},initial[[1]]]];
LaunchKernels[Length[toBeCalculated]];
ParallelDo[{timing,solList}=
findSolutionsWithCondition[curvedSFData,sl2cRules4CC,spinorRules4CC,areafRule,allvariablesp,rule4Bp,dihedralFromCurvedGeo,toBeCalculated[[i]],initial,immiriziValue,fileName[[i]],{15,10^-25}]//AbsoluteTiming;
Print[timing];
If[solList=="cannot find solution in some steps",Print["cannot find solution in some steps for ",toBeCalculated[[i]]];
],
{i,1,Length[toBeCalculated]}];
CloseKernels[]
]
]
