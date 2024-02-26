(* ::Package:: *)

deltaL[furureEdge_]:=\[Delta]L[1]


curvedCoors[simplex_,futureEdges_,ruleLabelVertex_,checkEqVal_:1/10]:=Block[{edges,futureEdgesInEq,otherEdges,variables,equsLHS,equsRHS,equsRHS2,equs,variablesInEq,fixedVariable,fixedVariableVal,sol,coorWithdeltal,forcheck,position,a,solvalue,equsValue,checkSolWithVal},
edges=Sort/@Subsets[simplex,{2}];
futureEdgesInEq=Cases[edges,_?(MemberQ[futureEdges,#]&)];
If[futureEdgesInEq=={},Return[ruleLabelVertex]];
otherEdges=DeleteCases[edges,_?(MemberQ[futureEdges,#]&)];
variables=Flatten[futureEdgesInEq]//DeleteDuplicates;
variables=GatherBy[variables,Sign[First[#]-5]&];
variables=Which[Equal@@(Length/@variables),Sort[variables]//Last,!Equal@@(Length/@variables),SortBy[variables,Length]//First];
variables=#->{t[First[#]],x[First[#]],y[First[#]],z[First[#]]}&/@variables;
equsLHS=edges/.variables;
equsLHS=equsLHS/.ruleLabelVertex;
equsLHS=(#[[2]]-#[[1]]).eta.(#[[2]]-#[[1]])&/@equsLHS;
equsRHS=futureEdgesInEq/.ruleLabelVertex;
equsRHS=(#[[2]]-#[[1]]).eta.(#[[2]]-#[[1]])&/@equsRHS;
equsRHS=equsRHS+deltaL/@futureEdgesInEq;
equsRHS=futureEdgesInEq->equsRHS//Thread;
equsRHS2=otherEdges/.ruleLabelVertex;
equsRHS2=(#[[2]]-#[[1]]).eta.(#[[2]]-#[[1]])&/@equsRHS2;
equsRHS2=otherEdges->equsRHS2//Thread;
equsRHS=Join[equsRHS,equsRHS2];
equsRHS=edges/.equsRHS;
equs=equsLHS==equsRHS//Thread;
equs=DeleteCases[equs,True];
equsRHS=equs[[All,2]];
variablesInEq=variables[[All,2]]//Flatten;
{fixedVariable,variablesInEq}=Which[Length[variablesInEq]==4,{{},variablesInEq},Length[variablesInEq]==8,{{FirstCase[variablesInEq,_t]},DeleteCases[variablesInEq,FirstCase[variablesInEq,_t]]}
];
fixedVariableVal=If[fixedVariable=!={},V@@@fixedVariable,{}]/.ruleLabelVertex;
fixedVariableVal=If[fixedVariableVal=!={},First/@fixedVariableVal,{}];
fixedVariable=Rule[fixedVariable,fixedVariableVal]//Thread;
equs=equs/.fixedVariable//Expand;
Off[Solve::ratnz];
sol=Solve[equs,variablesInEq]//Expand;
sol=Prepend[#,fixedVariable]&/@sol;
sol=Flatten/@sol;
coorWithdeltal=variables/.V[a_]:>Vp[a];
coorWithdeltal=coorWithdeltal/.sol;
forcheck={#,Vp@@#}&/@variables[[All,1]];
forcheck=forcheck/.ruleLabelVertex/.coorWithdeltal;
forcheck=Map[Norm[#[[1]]-#[[2]]]&,forcheck,{2}]/.\[Delta]L[_]->0//Chop;
position=Position[forcheck,{0..}|{0}]//Flatten;
sol=sol[[position]]//Flatten;
solvalue=sol/.\[Delta]L[_]:>checkEqVal;
equsValue=equs/.\[Delta]L[_]:>checkEqVal;
checkSolWithVal=And@@((List@@equsValue)/.solvalue);
If[!checkSolWithVal,Return["The solution of the coordinate is not good"]];
sol=(simplex/.variables/.sol/.ruleLabelVertex);
simplex->sol//Thread
]


wedge[{s1_,s2_}]:=Table[s1[[aind]]Conjugate[s2[[bind]]],{aind,1,2},{bind,1,2}]
spinorsParallelQ[{{l1:{l11_,l12_},l2:{l21_,l22_}},{l1p:{l11p_,l12p_},l2p:{l21p_,l22p_}}}]:=Block[{ifparallel,coes},
ifparallel={Abs[Conjugate[l1].l1p/(Norm[l1]Norm[l1p])],Abs[Conjugate[l2].l2p/(Norm[l2]Norm[l2p])]};
ifparallel=ifparallel=={1,1};
If[!ifparallel,Return[False]];
coes={Conjugate[l1].l1p/(Norm[l1]Norm[l1p]),Conjugate[l2].l2p/(Norm[l2]Norm[l2p])};
Norm[coes[[1]]coes[[2]]]==1||(coes[[1]]coes[[2]]==1)
]


getTransGroup[adjacentSpinorData_,"spacelike"]:=Block[{spinors,Jspinors,epsilon={{0,-1},{1,0}},bivector,bivector2,transGroups,transedbivector,projectedBivector,thephase,thephase1,thegroup,resultCheck},
spinors=(Transpose[#[[1]].Transpose[#[[2,1]]]]&/@#1)&/@adjacentSpinorData;
Jspinors=Map[epsilon.Conjugate[#]&,#1,{2}]&/@spinors;
bivector=wedge/@#&/@spinors;
bivector2=wedge/@#&/@Jspinors;
bivector=bivector-bivector2;
transGroups=adjacentSpinorData[[1]]//Transpose//First;
transedbivector=MapThread[ConjugateTranspose[#1].#2.#1&,{transGroups,#}]&/@bivector;
projectedBivector=(1/2 Tr[#.PauliMatrix[1]]PauliMatrix[1]+1/2 Tr[#.PauliMatrix[2]]PauliMatrix[2])&/@#1&/@transedbivector;
thephase=projectedBivector[[2,2,1,2]]/projectedBivector[[2,1,1,2]];
thephase1=ArcCos[1/2 (thephase+Conjugate[thephase])//Re];
thephase1=If[Cos[thephase1]+I Sin[thephase1]==thephase,thephase1,2 Pi-thephase1];
thephase=MatrixExp[-I thephase1 PauliMatrix[3]/2];
thegroup=transGroups[[1]].thephase.Inverse[transGroups[[2]]];
resultCheck=MapAt[Transpose[thegroup.Transpose[#]]&,#1,2]&/@spinors;
If[!(And@@spinorsParallelQ/@resultCheck),Print["wrong when glueing spacelike adjacent tetrahedra"];Return["wrong when glueing spacelike adjacent tetrahedra"]];
thegroup
]
(********)
getTransGroup[adjacentSpinorData_,"timelike"]:=Block[{alphaf,spinors,Jspinors,epsilon={{0,-1},{1,0}},bivector,bivector2,transGroups,transedbivector,projectedBivector,thephase,thephase1,thegroup,resultCheck},
alphaf=Which[adjacentSpinorData[[1,1,2,1]]=={{1,0},{1,0}},1,adjacentSpinorData[[1,1,2,1]]=={{0,1},{0,1}},-1,adjacentSpinorData[[1,1,2,1]]=={1/Sqrt[2] {1,1},1/Sqrt[2] {1,-1}},Return["the case to glue tetrahedra is out of our scope"]];
spinors=(Transpose[#[[1]].Transpose[#[[2,1]]]]&/@#1)&/@adjacentSpinorData;
Jspinors=Map[epsilon.Conjugate[#]&,#1,{2}]&/@spinors;
bivector=wedge/@#&/@spinors;
bivector=Map[PauliMatrix[3].#.PauliMatrix[3]&,#1]&/@bivector;
bivector2=wedge/@#&/@Jspinors;
bivector=bivector+bivector2;
transGroups=adjacentSpinorData[[1]]//Transpose//First;
transedbivector=MapThread[ConjugateTranspose[#1].#2.#1&,{transGroups,#}]&/@bivector;
projectedBivector=(1/2 Tr[#.PauliMatrix[1]]PauliMatrix[1]+1/2 Tr[#.PauliMatrix[2]]PauliMatrix[2])&/@#1&/@transedbivector;
thephase=projectedBivector[[2,2,1,2]]/projectedBivector[[2,1,1,2]];
thephase1=ArcCos[1/2 (thephase+Conjugate[thephase])//Re];
thephase1=If[Cos[thephase1]+I Sin[thephase1]==thephase,thephase1,2 Pi-thephase1];
thephase=MatrixExp[-alphaf I thephase1 PauliMatrix[3]/2];
thegroup=transGroups[[1]].thephase.Inverse[transGroups[[2]]];
resultCheck=MapAt[Transpose[thegroup.Transpose[#]]&,#1,2]&/@spinors;
If[!(And@@spinorsParallelQ/@resultCheck),Print["wrong when glueing timelike adjacent tetrahedra"];Return["wrong when glueing timelike adjacent tetrahedra"]];
thegroup
]


glueAdjacentSFData[adjacentSFData0_]/;Length[adjacentSFData0]==5:=adjacentSFData0
glueAdjacentSFData[adjacentSFData0_]/;Length[adjacentSFData0]==10:=Block[{adjacentSFData,adjacentSL2CData,adjacentSpinorData,forSort,spaceOrTimeLike,transformationGroup,adjacentSpinorDataTransed,adjacentSL2CDataTransed},
adjacentSFData=GroupBy[adjacentSFData0,Cases[#,Triangle[__],Infinity]&];
adjacentSL2CData=adjacentSFData[{}];
adjacentSpinorData=KeyDrop[adjacentSFData,{{}}]//Values;
forSort=Keys[adjacentSL2CData];
forSort=forSort->{1,2}//Thread;
adjacentSpinorData=SortBy[#1,(Most[Keys[#]]/.forSort&)]&/@adjacentSpinorData;
adjacentSpinorData=Thread[#,Rule]&/@adjacentSpinorData;
adjacentSpinorData=Association@@adjacentSpinorData;
spaceOrTimeLike=#[[All,2,2]]&/@adjacentSpinorData//Values//Flatten//DeleteDuplicates;
spaceOrTimeLike=If[Length[spaceOrTimeLike]==1,First[spaceOrTimeLike],(Print["the glued tetrahedra should be all timelike or all spacelike"];Return["the glued tetrahedra should be all timelike or all spacelike"])];
transformationGroup=getTransGroup[adjacentSpinorData,spaceOrTimeLike];
adjacentSpinorData=First/@adjacentSpinorData;
adjacentSpinorData=ConstantArray[#,2]&/@adjacentSpinorData//Normal;
adjacentSpinorDataTransed=Thread[#]&/@adjacentSpinorData;
adjacentSL2CData=adjacentSL2CData//Association;
adjacentSL2CDataTransed=MapAt[#.Inverse[transformationGroup]&,adjacentSL2CData,2]//Normal;
{adjacentSL2CDataTransed,adjacentSpinorDataTransed}//Flatten
]


getSFDataFromCurvedComplex[ruleLabelVertexCurvedGeometry_,simplicesInLabel_,bdyTetrahedraSorted_]:=Block[{sfDataCurved,sfData,unConsistentOrientation,allTetrahedra,bdyTetrahedraInSimplex,bdyspinors,simplicesByTetrahedra,connectionRelation,graphInner,searchOrder,consistentOrientation,allTriangles,areas,arearule,equalAreaQ,simplexByTriangles,orientatedTriangles},
sfDataCurved=MapThread[getSFDataFromSingleSimplex[#1,#2]&,{ruleLabelVertexCurvedGeometry,simplicesInLabel}];
{sfData,unConsistentOrientation}=sfDataCurved//Transpose;
allTetrahedra=Subsets[#,{4}]&/@simplicesInLabel;
allTetrahedra=Sort/@allTetrahedra;
bdyTetrahedraInSimplex=GroupBy[#,MemberQ[bdyTetrahedraSorted,#]&]&/@allTetrahedra;
bdyTetrahedraInSimplex=#[True]&/@bdyTetrahedraInSimplex;
bdyspinors=MapThread[Function[u,getBdySpinor[u,#2,eta]]/@#1&,{bdyTetrahedraInSimplex,ruleLabelVertexCurvedGeometry}]//Flatten//Dispatch;
sfData=sfData//Flatten;
sfData=GroupBy[sfData,Keys[#][[2]]&];
sfData=Map[glueAdjacentSFData,sfData]//Values//Flatten;
unConsistentOrientation=unConsistentOrientation//Flatten;
simplicesByTetrahedra=Cases[sfData,{Simplex[__],Tetrahedron[__]},Infinity];
connectionRelation=findConnection[simplicesByTetrahedra];
graphInner=UndirectedEdge@@@connectionRelation;
searchOrder=FindPath[graphInner,Simplex@@(simplicesInLabel//First),Simplex@@(simplicesInLabel//Last//Sort),{Length[simplicesInLabel]-1}]//Flatten;
consistentOrientation=Nest[adjustOrientation,{unConsistentOrientation,searchOrder,0},Length[searchOrder]]//Dispatch;
allTriangles=Subsets[#,{3}]&/@simplicesInLabel;
allTriangles=Apply[Triangle,allTriangles,{2}];
allTriangles=allTriangles/.Triangle[x__]:>Sort[Triangle[x]];
areas=MapThread[Function[u,trigAreaIn4D[u,#2]]/@#1&,{allTriangles,ruleLabelVertexCurvedGeometry}];
arearule=Rule[allTriangles,areas]//Thread;
arearule=Thread/@arearule//Flatten;
arearule=GroupBy[arearule,Keys,Values];
equalAreaQ=If[Length[#]==1,True,Norm[Differences[#] ]==0]&/@arearule;
equalAreaQ=And@@equalAreaQ;
If[!equalAreaQ,(Print["areas of the same triangle is not the same"];Return["areas of the same triangle is not the same"])];
arearule=First/@arearule;
allTriangles=Keys[arearule];
arearule=arearule//Normal//Dispatch;
simplexByTriangles=Cases[sfData,{Simplex[__],Tetrahedron[__],Triangle[__]},Infinity];
simplexByTriangles=simplexByTriangles//GroupBy[#,Last]&;
orientatedTriangles=Fold[orientingTriangles[#2,#1,consistentOrientation]&,simplexByTriangles,allTriangles]//Normal;
sfData=sfData//Dispatch;
{sfData,arearule,bdyspinors,orientatedTriangles,consistentOrientation}
]
