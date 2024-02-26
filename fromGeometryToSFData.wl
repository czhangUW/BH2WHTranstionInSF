(* ::Package:: *)

trigAreaIn4D[Triangle[vertexLabel__],ruleLabelVertex_]:=Block[{x,y,z,basis1,basis2,area,indexaa,indexbb,indexcc,indexdd},
{x,y,z}={vertexLabel}/.ruleLabelVertex;
{basis1,basis2}={y-x,z-x};
area=Table[Sum[epsilon[[indexaa,indexbb,indexcc,indexdd]]basis1[[indexaa]]basis2[[indexbb]],{indexaa,1,4},{indexbb,1,4}],{indexcc,1,4},{indexdd,1,4}];
area=1/8  Tr[area.eta.area.eta]//Abs//Sqrt
]


getTetrahedronNormal[tetrahedron_,metric_:eta]:=Block[{basepoint,basis1,basis2,basis3,normal,normalize},
basepoint=tetrahedron[[1]];
{basis1,basis2,basis3}=(#-basepoint)&/@tetrahedron[[2;;4]];
normal=Table[Sum[LeviCivitaTensor[4][[ii,jj,kk,ll]]basis1[[jj]]basis2[[kk]]basis3[[ll]],{jj,1,4},{kk,1,4},{ll,1,4}],{ii,1,4}];
normal=metric.normal;
normalize=normal.metric.normal;
normal=normal/Sqrt[Abs[normalize]];
If[normalize<0,Return[Sign[normal[[1]]]normal]];
If[normalize>0,Return[Sign[normal[[-1]]]normal]];
]
(*This is the old version,to get outward normal*)
(*getTetrahedronNormal[tetrahedron_,theOtherVertex_]:=Block[{basepoint,basis1,basis2,basis3,normal,normalize,anOutwardVec},
basepoint=tetrahedron[[1]];
{basis1,basis2,basis3}=(#-basepoint)&/@tetrahedron[[2;;4]];
normal=Table[Sum[LeviCivitaTensor[4][[ii,jj,kk,ll]]basis1[[jj]]basis2[[kk]]basis3[[ll]],{jj,1,4},{kk,1,4},{ll,1,4}],{ii,1,4}];
normal=eta.normal;
anOutwardVec=basepoint-theOtherVertex;
normal =normal Sign[anOutwardVec.eta.normal];
normalize=normal.eta.normal;
normal=normal/Sqrt[Abs[normalize]];
normal
]*)


myToSphericalCoordinates[n_]/;Norm[n[[1;;2]]]<10^-chopdelta:=If[n[[3]]>0,{n[[3]],0,0}//N[#,precise]&,{-n[[3]],Pi,0}//N[#,precise]&]
myToSphericalCoordinates[n_]:=ToSphericalCoordinates[n]

getSL2C[n1_]/;Norm[n1-{1,0,0,0}]<10^-chopdelta||Norm[n1-{0,0,0,1}]<10^-chopdelta:=IdentityMatrix[2]//N[#,precise]&
getSL2C[n1_]/;Norm[n1-{0,0,0,-1}]<10^-chopdelta:={{0,-I},{-I,0}}//N[#,precise]&
getSL2C[n1_]:=Block[{rn,thetan,phin,gsut,forBoost,gBoost,gsl2c},
{rn,thetan,phin}=myToSphericalCoordinates[n1[[2;;4]]];
gsut={{Cos[thetan/2],E^(-I phin) Sin[thetan/2]},{-E^(I phin) Sin[thetan/2],Cos[thetan/2]}};
forBoost=SortBy[{n1[[1]],rn},#^2&]//First;
gBoost={{1/Sqrt[forBoost+Sqrt[1+forBoost^2]],0},{0,Sqrt[forBoost+Sqrt[1+forBoost^2]]}};
gsl2c=gBoost.gsut]
getSO13[sl2cg_]:=Table[1/2 Tr[sl2cg.sigma4[[j]].ConjugateTranspose[sl2cg].sigma4[[i]]]//Re,{i,1,4},{j,1,4}]
(*the result transforms the normal vector to  (1,0,0,0) or (0,0,0,1). Thus it is the inverse of the spin foam SL(2,C) element*)


unNormalizedFacesBiNormals[ruleLabelVertices_,verticesLabel_,metric_:eta]:=Block[{facesLabel,faces,facesEdgeVec,binormalLowerIndices,binormal},
facesLabel=Subsets[verticesLabel,{3}];
facesLabel=Sort/@facesLabel;(*(1): This sort assigns a fixed orientation to each face, regardless of whether the face belongs to tetrahedra of two different 4-simplices*)
faces=facesLabel/.ruleLabelVertices;
facesEdgeVec=#[[2;;3]]-{#[[1]],#[[1]]}&/@faces;
binormalLowerIndices=Table[Sum[epsilon[[mm,nn,ii,jj]]#[[1]][[ii]]#[[2]][[jj]],{ii,1,4},{jj,1,4}],{mm,1,4},{nn,1,4}]&/@facesEdgeVec;
binormal=metric.#.metric&/@binormalLowerIndices;
Rule@@@({facesLabel,binormal}//Transpose)
]
(*unNormalizedFacesBiNormals[ruleLabelVertices_,verticesLabel_,metric_:eta]:=Block[{facesLabel,faces,facesEdgeVec,binormalLowerIndices,binormal},
facesLabel=Subsets[verticesLabel,{3}];
faces=facesLabel/.ruleLabelVertices;
faces=Sort/@faces;(*(1): This sort assigns a fixed orientation to each face, regardless of whether the face belongs to tetrahedra of two different 4-simplices*)
facesEdgeVec=#[[2;;3]]-{#[[1]],#[[1]]}&/@faces;
binormalLowerIndices=Table[Sum[epsilon[[mm,nn,ii,jj]]#[[1]][[ii]]#[[2]][[jj]],{ii,1,4},{jj,1,4}],{mm,1,4},{nn,1,4}]&/@facesEdgeVec;
binormal=metric.#.metric&/@binormalLowerIndices;
Rule@@@({Sort/@facesLabel,binormal}//Transpose)
(*Here we Sort the facesLabel just for applying  the resulting rule in the future. The order of the facelabel could be different from  the orientation of the triangle introduced in (1)*)
]*)


(*here the condition tetrahedronNormalInBoundary.eta.tetrahedronNormalInBoundary>0 implies tetrahedronNormalInBoundary\[Equal]{0,0,0,1} since tetrahedronNormalInBoundary can either be {1,0,0,0} or {0,0,0,1}. However, because the input
 tetrahedronNormalInBoundary can be {0,0,0,0,99999999}, we'd better use the former one*)
geometricSpinorFromThreeNormal[faces3NormalsIn4D_,sortedFacesLabel_,tetrahedronNormalInBoundary_,tetrahedraLabel_,simplexLabel_]/;tetrahedronNormalInBoundary.eta.tetrahedronNormalInBoundary>0:=
Block[{eta3d=DiagonalMatrix[{-1,1,1}],basis3d={PauliMatrix[0],PauliMatrix[1],PauliMatrix[2]},norm,threeNormal,sign,rotation,threeNormalRotated,threeNormal2Pauli,boost,su11,basicSpinor,simplexTetraTrig},
threeNormal=Most/@faces3NormalsIn4D;
norm=#.eta3d.#&/@threeNormal;
sign=MapThread[If[#1>0,-1,Sign[#2[[1]]]]&,{norm,threeNormal}];
threeNormal=MapThread[#1 #2/Sqrt[Abs[#3]]&,{sign,threeNormal,norm}];
threeNormal2Pauli=#.basis3d&/@threeNormal;
rotation=Arg[I #[[2]]+#[[3]]]&/@threeNormal;
rotation={{E^(-((I #)/2)),0},{0,E^((I #)/2)}}&/@rotation;
threeNormalRotated=MapThread[#1.#2.ConjugateTranspose[#1]&,{rotation,threeNormal2Pauli}];
threeNormalRotated=Function[u,1/2 Tr[#.u]//Re]/@basis3d&/@threeNormalRotated;
boost=If[#[[3]]^2>#[[1]]^2,#[[1]],#[[3]]]&/@threeNormalRotated;
boost=ArcSinh/@boost;
boost={{Cosh[#/2],I Sinh[#/2]},{-I Sinh[#/2],Cosh[#/2]}}&/@boost;
su11=MapThread[#1.#2&,{boost,rotation}];
basicSpinor=MapThread[If[#1>0,{{1/Sqrt[2] {1,1},1/Sqrt[2] {1,-1}},"timelike"},If[#2>0,{{{1,0},{1,0}},"timelike"},{{{0,1},{0,1}},"timelike"}]]&,{norm,sign}];
(*MapThread[Function[u,ConjugateTranspose[#1].u]/@#2&,{su11,basicSpinor}]*)
(******)
simplexTetraTrig={Simplex@@simplexLabel,Tetrahedron@@tetrahedraLabel,Triangle@@@sortedFacesLabel}//Thread;
Rule[simplexTetraTrig,{ConjugateTranspose/@su11,basicSpinor}//Transpose]//Thread
]


geometricSpinorFromThreeNormal[faces3NormalsIn4D_,sortedFacesLabel_,tetrahedronNormalInBoundary_,tetrahedraLabel_,simplexLabel_]/;tetrahedronNormalInBoundary.eta.tetrahedronNormalInBoundary<0:=
Block[{threeNormal,sphericalCoor3Normal,rotation,simplexTetraTrig},
threeNormal=Rest/@faces3NormalsIn4D;
threeNormal=#/Sqrt[#.#]&/@threeNormal;
sphericalCoor3Normal=If[Norm[#-{0,0,1}]<10^-chopdelta,{1,0,0}//N[#,precise]&,If[Norm[#-{0,0,-1}]<10^-chopdelta,{1,Pi,0}//N[#,precise]&,ToSphericalCoordinates[#]]]&/@threeNormal;
rotation={{Cos[#[[2]]/2],E^(-I #[[3]]) Sin[#[[2]]/2]},{-E^(I #[[3]]) Sin[#[[2]]/2],Cos[#[[2]]/2]}}&/@sphericalCoor3Normal;
simplexTetraTrig={Simplex@@simplexLabel,Tetrahedron@@tetrahedraLabel,Triangle@@@sortedFacesLabel}//Thread;
(*{ConjugateTranspose[#].{1,0},ConjugateTranspose[#].{1,0}}&/@rotation*)
Rule[simplexTetraTrig,{ConjugateTranspose[#],{{{1,0},{1,0}},"spacelike"}}&/@rotation]//Thread
]


(*geometricspinors2Bivector[geometricspinors_,tetrahedronNormalInBoundary_,faceNormalInBdy_]:=Block[{bivector,epsilon={{0,-1},{1,0}},bivector2,factor},
bivector=Table[#[[1,a]]Conjugate[#[[2,b]]],{a,1,2},{b,1,2}]&/@geometricspinors;
bivector2=Transpose/@bivector;
bivector=If[tetrahedronNormalInBoundary\[Equal]{1,0,0,0},#,PauliMatrix[3].#]&/@bivector;
bivector2=If[tetrahedronNormalInBoundary\[Equal]{1,0,0,0},-epsilon.#.epsilon,epsilon.#.epsilon.PauliMatrix[3]]&/@bivector2;
bivector=bivector-bivector2;
If[tetrahedronNormalInBoundary\[Equal]{1,0,0,0},Return[bivector]];
factor=If[#.eta.#<0,Sign[#[[1]]],I]&/@faceNormalInBdy;
MapThread[#1 #2&,{factor,bivector}]
]*)


getOrientation[faces3NormalsIn4D_,sortedFacesLabel_,tetrahedraLabel_,simplexLabel_]:=Block[{facesLabelp,x,rule,variables,eqs,eqs1,sol,solvedVariable,initialdata,n,tetrahedron,orientationValue,faceTetrahedSimplexraLabel,resultcheck},
facesLabelp=Flatten[sortedFacesLabel,1]//DeleteDuplicates;
rule=Rule[facesLabelp,x/@Range[Length[facesLabelp]]]//Thread;
variables=sortedFacesLabel/.rule;
Do[eqs[a]=variables[[a]].faces3NormalsIn4D[[a]]=={0,0,0,0}//Thread,{a,1,5}];
eqs1={variables[[1,1]]==N[1,precise]};
sol[1]=Solve[Join[eqs[1],eqs1]//Chop,variables[[1]]]//Flatten;
Do[solvedVariable=Cases[variables[[n+1]],_?(MemberQ[variables[[n]],#]&)];
initialdata=-solvedVariable/.sol[n];
eqs1=Distribute[solvedVariable==initialdata,List];
sol[n+1]=NSolve[Join[eqs[n+1],eqs1]//Chop,variables[[n+1]]]//Flatten,
{n,1,4}
];
faceTetrahedSimplexraLabel=Thread/@({Simplex@@simplexLabel,Tetrahedron@@@tetrahedraLabel,Apply[Triangle,sortedFacesLabel,{2}]}//Thread);
orientationValue=Table[variables[[a]]/.sol[a],{a,1,5}]/.{x_/;Abs[x-1]<10^-10:>1,x_/;Abs[x+1]<10^-10:>-1};
orientationValue=Thread/@(Rule[faceTetrahedSimplexraLabel,orientationValue]//Thread);
resultcheck=GatherBy[Flatten[orientationValue,1],#[[1,3]]&];
resultcheck=(#[[1,2]]+#[[2,2]]==0)&/@resultcheck//And@@#&;
If[resultcheck,Return[orientationValue//Flatten]];
Print["cannot find a consitent orientation for faces", sortedFacesLabel]
]


getSFDataFromSingleSimplex[ruleLabelVertex_,simplexInLabel_]:=Block[{verticesLabel,tetrahedraInLabel,tetrahedra,normals,gSL2C,gSO13,spinforamSL2C,normalsInBoundary,faceBiNormalAtVertex,facesLabel,facesBinormalsAtRef,faces3NormalsIn4D,geometricspinors,orientation,result},
verticesLabel=Flatten[simplexInLabel];
tetrahedraInLabel=Subsets[verticesLabel,{4}];
tetrahedra=tetrahedraInLabel/.ruleLabelVertex;
normals=Map[getTetrahedronNormal,tetrahedra];
(******)
gSL2C=getSL2C/@normals;
gSO13=getSO13/@gSL2C;
spinforamSL2C=Inverse/@gSL2C;
normalsInBoundary=MapThread[Dot,{gSO13,normals}]//Chop;
faceBiNormalAtVertex=unNormalizedFacesBiNormals[ruleLabelVertex,verticesLabel];
facesLabel=(Sort/@Subsets[#,{3}])&/@tetrahedraInLabel;
faceBiNormalAtVertex=facesLabel/.faceBiNormalAtVertex;
facesBinormalsAtRef=MapThread[Function[u,#1.u.Transpose[#1]]/@#2&,{gSO13,faceBiNormalAtVertex}];
faces3NormalsIn4D=MapThread[Function[u,u.eta.#1]/@#2&,{normalsInBoundary,facesBinormalsAtRef}];
geometricspinors=MapThread[geometricSpinorFromThreeNormal[#1,#2,#3,#4,simplexInLabel]&,{faces3NormalsIn4D,facesLabel,normalsInBoundary,tetrahedraInLabel}]//Flatten;
orientation=getOrientation[faces3NormalsIn4D,facesLabel,tetrahedraInLabel,simplexInLabel];
tetrahedra={Simplex@@simplexInLabel,Tetrahedron@@@tetrahedraInLabel}//Thread;
spinforamSL2C=Rule[tetrahedra,spinforamSL2C]//Thread;
result={{spinforamSL2C,geometricspinors}//Flatten,orientation}//Chop[#,10^-chopdelta]&;
result=result/.{Triangle[x__]:>Sort[Triangle[x]],Tetrahedron[x__]:>Sort[Tetrahedron[x]],Simplex[x__]:>Sort[Simplex[x]]}
(*Here we sort these objects for applying the rules in the future*)
]


getBdySpinor[bdyTetrahedraLabel_,ruleLabelVertex_,metric_]:=Block[{bdyTetrahedravertex,tetrahedronNormal,gSL2C,gSO13,normalsInBoundary,facelabels,faceBiNormal,facesBinormalsTransformed,faces3NormalsIn4D,geometricspinors,result},
bdyTetrahedravertex=bdyTetrahedraLabel/.ruleLabelVertex;
tetrahedronNormal=getTetrahedronNormal[bdyTetrahedravertex,metric];
gSL2C=getSL2C[tetrahedronNormal];
gSO13=getSO13[gSL2C];
normalsInBoundary=Dot[gSO13,tetrahedronNormal]//Chop;
(*Here we use chop because normalsInBoundary is either {1,0,0,0} or {0,0,0,1}*)
{facelabels,faceBiNormal}=(List@@@unNormalizedFacesBiNormals[ruleLabelVertex,bdyTetrahedraLabel,metric])//Transpose;
facesBinormalsTransformed=gSO13.#.Transpose[gSO13]&/@faceBiNormal;
faces3NormalsIn4D=#.eta.normalsInBoundary&/@facesBinormalsTransformed;
geometricspinors=geometricSpinorFromThreeNormal[faces3NormalsIn4D,facelabels,normalsInBoundary,bdyTetrahedraLabel,"bdy"];
result=MapAt[Rest,geometricspinors,{All,1}]//Chop[#,10^-chopdelta]&;
result=result/.{Triangle[x__]:>Sort[Triangle[x]],Tetrahedron[x__]:>Sort[Tetrahedron[x]]}
]


changeOrientation[tobeChanged_]:=Block[{result},
result=List@@@tobeChanged//Transpose;
result={result[[1]],-result[[2]]}//Transpose;
result=Rule@@@result
]


findConnection[simplicesByTetrahedra_]:=Block[{labelledTetrahedraBySimplex,tetrahedraInner,connectionRelation},
labelledTetrahedraBySimplex=GatherBy[simplicesByTetrahedra,Last];
tetrahedraInner=Cases[labelledTetrahedraBySimplex,_?(Length[#]==2&)];
connectionRelation=First/@Transpose/@tetrahedraInner
]


adjustOrientation[{unConsistentOrientation_,searchOrder_,alreadyChanged_}]/;alreadyChanged<=Length[searchOrder]-2:=Block[{simplicesToBeAdjested,asReference,toBeChanged,x,consistentQ,changedOrientation,y},
simplicesToBeAdjested=searchOrder[[{alreadyChanged+1,alreadyChanged+2}]];
{asReference,toBeChanged}=Cases[unConsistentOrientation,x_/;MemberQ[First[x],#]]&/@simplicesToBeAdjested;
consistentQ=Cases[GatherBy[{asReference,toBeChanged}//Flatten,(First[#][[{2,3}]])&],_?(Length[#]==2&)];
consistentQ=Cases[consistentQ,_?(Total[#[[All,2]]]!=0&)];
If[consistentQ==={},Return[{unConsistentOrientation,searchOrder,alreadyChanged+1}]];
changedOrientation=toBeChanged/.(x_->y_):>(x->-y);
changedOrientation=Rule[toBeChanged,changedOrientation]//Thread//Dispatch;
{unConsistentOrientation/.changedOrientation,searchOrder,alreadyChanged+1}
]
adjustOrientation[{unConsistentOrientation_,searchOrder_,alreadyChanged_}]/;alreadyChanged==Length[searchOrder]-1:=Block[{theUnConsistent},
theUnConsistent=Cases[GatherBy[unConsistentOrientation,(First[#][[2;;3]])&],_?(Length[#]==2&)];
theUnConsistent=Cases[theUnConsistent,_?(Total[#[[All,2]]]!=0&)];
If[theUnConsistent!={},Return["Cannot find consistent orientation"]];
unConsistentOrientation
]


orientingTriangles[triangle_,TriangleToSimplexTetrahedron_Association,orientationrule_]:=Block[{TriangleBySimplexTetrahedron,g,boundaryQ,ifBoundary,verticesg,endpoints,thepath,orderedSimlexTetrahedron,checkresult,orientedTriangles,triangleOrientation,orientedTriangleToSimplexTetrahedron},
TriangleBySimplexTetrahedron=Most/@TriangleToSimplexTetrahedron[triangle];
g=Graph[UndirectedEdge@@@TriangleBySimplexTetrahedron];
verticesg=VertexList[g];
boundaryQ=AcyclicGraphQ[g];(*True means it is boundary triangle*)
endpoints=If[boundaryQ,Position[VertexDegree[g],1]//Flatten,Position[verticesg,_Simplex]//Flatten];
(*This will ensure that for internel face, the path  starts from Simplex[_]. (see below labelled by 1)*)
endpoints=verticesg[[endpoints[[1;;2]]]];
(*For close graph, we choose any two vertices as the endpoint. Then, after we find a path connecting the two vertice, we will us the first two elements of the path as our final endpoint because thery are adjecent*)
If[!boundaryQ,endpoints=FindPath[g,endpoints[[1]],endpoints[[2]]]//First ;endpoints=endpoints[[{1,2}]]];(*1*)
thepath=FindPath[g,endpoints[[1]],endpoints[[2]],{Length[verticesg]-1}]//First;
If[!boundaryQ,thepath=Append[thepath,thepath//First]];
orderedSimlexTetrahedron=Partition[thepath,2,1];
orderedSimlexTetrahedron=SortBy[#,#/.{x_Tetrahedron:>1,y_Simplex:>0}&]&/@orderedSimlexTetrahedron;
checkresult=And@@(MemberQ[TriangleBySimplexTetrahedron,#]&/@orderedSimlexTetrahedron);
If[!checkresult,Print["sort of the face edges counter problems"];Return[]];
triangleOrientation=(Append[#,triangle]&/@orderedSimlexTetrahedron)/.orientationrule;
If[!MatchQ[Total/@Partition[triangleOrientation,2,1],{0..}],Print["the orientation counter problems"];Return[]];
If[boundaryQ&&triangleOrientation[[1]]==-1,orderedSimlexTetrahedron=Reverse[orderedSimlexTetrahedron]];
(*for boundary face, the orientation start from the boundary vertex which is not shown in orderedSimlexTetrahedron. The first element in orderedSimlexTetrahedron corresponds to the half edge and the vertex connecting the boundary  vertex*)
If[(!boundaryQ)&&triangleOrientation[[1]]==1,orderedSimlexTetrahedron=Reverse[orderedSimlexTetrahedron]];
(*for internal face, the orientation start from a vertex and move to the half edge connected with it. Thus, the sign for the starting half edge should be -1*)
orientedTriangleToSimplexTetrahedron=TriangleToSimplexTetrahedron;
orientedTriangleToSimplexTetrahedron[triangle]=(Append[orderedSimlexTetrahedron,boundaryQ]/.{True->"boundary",False->"internal"});
orientedTriangleToSimplexTetrahedron
]


getSFDataFromFlatComplex[ruleLabelVertex_,simplicesInLabel_,bdyTetrahedra_]/;Length[simplicesInLabel]==1:=Block[{sfData,unConsistentOrientation,bdyspinors,simplicesByTetrahedra,simplexByTriangles,allTriangles,arearule,orientatedTriangles},
{sfData,unConsistentOrientation}=getSFDataFromSingleSimplex[ruleLabelVertex,#]&/@simplicesInLabel//Transpose;
bdyspinors=getBdySpinor[#,ruleLabelVertex,eta]&/@bdyTetrahedra//Flatten//Dispatch;
unConsistentOrientation=Flatten[unConsistentOrientation];
sfData=sfData//Flatten;
simplexByTriangles=Cases[sfData,{Simplex[__],Tetrahedron[__],Triangle[__]},Infinity];
simplexByTriangles=simplexByTriangles//GroupBy[#,Last]&;
allTriangles=Keys[simplexByTriangles];
arearule=Rule[allTriangles,trigAreaIn4D[#,ruleLabelVertex]&/@allTriangles]//Thread//Dispatch;
orientatedTriangles=Fold[orientingTriangles[#2,#1,unConsistentOrientation]&,simplexByTriangles,allTriangles]//Normal;
sfData=sfData//Dispatch;
{sfData,arearule,bdyspinors,orientatedTriangles,unConsistentOrientation}
]

(********)
getSFDataFromFlatComplex[ruleLabelVertex_,simplicesInLabel_,bdyTetrahedra_]:=Block[{sfData,unConsistentOrientation,bdyspinors,simplicesByTetrahedra,connectionRelation,graphInner,searchOrder,consistentOrientation,simplexByTriangles,allTriangles,arearule,orientatedTriangles},
{sfData,unConsistentOrientation}=getSFDataFromSingleSimplex[ruleLabelVertex,#]&/@simplicesInLabel//Transpose;
bdyspinors=getBdySpinor[#,ruleLabelVertex,eta]&/@bdyTetrahedra//Flatten//Dispatch;
unConsistentOrientation=Flatten[unConsistentOrientation];
sfData=sfData//Flatten;
simplicesByTetrahedra=Cases[sfData,{Simplex[__],Tetrahedron[__]},Infinity];
connectionRelation=findConnection[simplicesByTetrahedra];
graphInner=UndirectedEdge@@@connectionRelation;
searchOrder=FindPath[graphInner,Simplex@@(simplicesInLabel//First),Simplex@@(simplicesInLabel//Last//Sort),{Length[simplicesInLabel]-1}]//Flatten;
consistentOrientation=Nest[adjustOrientation,{unConsistentOrientation,searchOrder,0},Length[searchOrder]]//Dispatch;
simplexByTriangles=Cases[sfData,{Simplex[__],Tetrahedron[__],Triangle[__]},Infinity];
simplexByTriangles=simplexByTriangles//GroupBy[#,Last]&;
allTriangles=Keys[simplexByTriangles];
arearule=Rule[allTriangles,trigAreaIn4D[#,ruleLabelVertex]&/@allTriangles]//Thread//Dispatch;
orientatedTriangles=Fold[orientingTriangles[#2,#1,consistentOrientation]&,simplexByTriangles,allTriangles]//Normal;
sfData=sfData//Dispatch;
{sfData,arearule,bdyspinors,orientatedTriangles,consistentOrientation}
]
