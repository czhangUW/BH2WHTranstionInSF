(* ::Package:: *)

doTriangulation[{origionalObjects_,futureBdy_},{dynamicalVertex_,evolveDynamicalVertex_}]:=Block[{evolvedBdy,unEvolvedBdy,futureBdyp,origionalObjectsp},
evolvedBdy=Cases[futureBdy,_?(MemberQ[#,dynamicalVertex]&)];
unEvolvedBdy=DeleteCases[futureBdy,_?(MemberQ[#,dynamicalVertex]&)];
futureBdyp=evolvedBdy/.dynamicalVertex->evolveDynamicalVertex;
futureBdyp=Join[futureBdyp,unEvolvedBdy];
origionalObjectsp=Append[#,evolveDynamicalVertex]&/@evolvedBdy;
origionalObjectsp=Join[origionalObjects,origionalObjectsp];
{origionalObjectsp,futureBdyp}
]


simpliciesAndTheirBdy[pastTetrahedra_,{dynamicalVertices_,evolveDynamicalVertices_}]:=Block[{pastTriangles,boundaryTriangles,fourSimplices,futureTetrahedra,otherBdyTetrahedra,futureBdyTrig,bdyTetrahedra},
pastTriangles=Subsets[#,{3}]&/@pastTetrahedra;
pastTriangles=Sort/@Flatten[pastTriangles,1];
pastTriangles=Gather[pastTriangles];
boundaryTriangles=Cases[pastTriangles,_?(Length[#]==1&)];
boundaryTriangles=Flatten[boundaryTriangles,1];
{fourSimplices,futureTetrahedra}=Fold[doTriangulation,{{},pastTetrahedra},{dynamicalVertices,evolveDynamicalVertices}//Transpose];
{otherBdyTetrahedra,futureBdyTrig}=Fold[doTriangulation,{{},boundaryTriangles},{dynamicalVertices,evolveDynamicalVertices}//Transpose];
bdyTetrahedra={pastTetrahedra,futureTetrahedra,otherBdyTetrahedra};
{fourSimplices,bdyTetrahedra}
]


gatherData[{data_,datap_}]:=Block[{samesdata,otherdata},
samesdata=data[[Position[#-data[[1]]&/@data//Chop[#,10^-6]&,{0..}]//Flatten]];
otherdata=DeleteCases[data,_?(MemberQ[samesdata,#]&)];
samesdata=Append[datap,samesdata//First];
{otherdata,samesdata}
]
