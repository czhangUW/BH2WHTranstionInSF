(* ::Package:: *)

(*jacobin=D[{r Sin[\[Theta]]Cos[\[Phi]],r Sin[\[Theta]]Sin[\[Phi]],r Cos[\[Theta]]},{{r,\[Theta],\[Phi]}}]//Inverse//FullSimplify;
metric=Transpose[jacobin].{{1-\[Beta]^2,0,0},{0,r^2,0},{0,0,r^2Sin[\[Theta]]^2}}.jacobin//FullSimplify;
metric/.{r\[Rule]Sqrt[x^2+y^2+z^2],\[Phi]\[Rule]Sign[y]ArcCos[x/Sqrt[x^2+y^2]],\[Theta]\[Rule]ArcCos[z/Sqrt[x^2+y^2+z^2]]}//FullSimplify[#,x>0&&y>0&&z>0]&*)


metricFun[x_,y_,z_,\[Beta]_]:={{1-(x^2 \[Beta]^2)/(x^2+y^2+z^2),-((x y \[Beta]^2)/(x^2+y^2+z^2)),-((x z \[Beta]^2)/(x^2+y^2+z^2))},{-((x y \[Beta]^2)/(x^2+y^2+z^2)),1-(y^2 \[Beta]^2)/(x^2+y^2+z^2),-((y z \[Beta]^2)/(x^2+y^2+z^2))},{-((x z \[Beta]^2)/(x^2+y^2+z^2)),-((y z \[Beta]^2)/(x^2+y^2+z^2)),1-(z^2 \[Beta]^2)/(x^2+y^2+z^2)}}


extrinsicKFun[x_,y_,z_,\[Beta]_,\[Alpha]_:alphaValue]:={{-((Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)] ((y^2+z^2) (x^2+y^2+z^2)^2 \[Beta]^2+M^2 \[Alpha] (2 x^2+(y^2+z^2) (-1+\[Beta]^2))-M (x^2+y^2+z^2)^(3/2) (x^2+2 (y^2+z^2) (-1+\[Beta]^2))))/((x^2+y^2+z^2)^(9/2) \[Beta]^2-2 M (x^2+y^2+z^2)^4 (-1+\[Beta]^2)+M^2 (x^2+y^2+z^2)^(5/2) \[Alpha] (-1+\[Beta]^2))),-((x y Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)] (-(x^2+y^2+z^2)^2 \[Beta]^2-M^2 \[Alpha] (-3+\[Beta]^2)+M (x^2+y^2+z^2)^(3/2) (-3+2 \[Beta]^2)))/((x^2+y^2+z^2)^(9/2) \[Beta]^2-2 M (x^2+y^2+z^2)^4 (-1+\[Beta]^2)+M^2 (x^2+y^2+z^2)^(5/2) \[Alpha] (-1+\[Beta]^2))),(x z Sqrt[(x^2+y^2)/(x^2+y^2+z^2)] ((x^2+y^2+z^2)^(5/2) \[Beta]^2+M^2 Sqrt[x^2+y^2+z^2] \[Alpha] (-3+\[Beta]^2)-M (x^2+y^2+z^2)^2 (-3+2 \[Beta]^2)))/(Sqrt[x^2+y^2] (x^2+y^2+z^2)^(5/2) Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)])},{-((x y Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)] (-(x^2+y^2+z^2)^2 \[Beta]^2-M^2 \[Alpha] (-3+\[Beta]^2)+M (x^2+y^2+z^2)^(3/2) (-3+2 \[Beta]^2)))/((x^2+y^2+z^2)^(9/2) \[Beta]^2-2 M (x^2+y^2+z^2)^4 (-1+\[Beta]^2)+M^2 (x^2+y^2+z^2)^(5/2) \[Alpha] (-1+\[Beta]^2))),-((Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)] ((x^2+z^2) (x^2+y^2+z^2)^2 \[Beta]^2+M^2 \[Alpha] (2 y^2+x^2 (-1+\[Beta]^2)+z^2 (-1+\[Beta]^2))-M (x^2+y^2+z^2)^(3/2) (y^2+2 x^2 (-1+\[Beta]^2)+2 z^2 (-1+\[Beta]^2))))/((x^2+y^2+z^2)^(9/2) \[Beta]^2-2 M (x^2+y^2+z^2)^4 (-1+\[Beta]^2)+M^2 (x^2+y^2+z^2)^(5/2) \[Alpha] (-1+\[Beta]^2))),(y z Sqrt[(x^2+y^2)/(x^2+y^2+z^2)] ((x^2+y^2+z^2)^(5/2) \[Beta]^2+M^2 Sqrt[x^2+y^2+z^2] \[Alpha] (-3+\[Beta]^2)-M (x^2+y^2+z^2)^2 (-3+2 \[Beta]^2)))/(Sqrt[x^2+y^2] (x^2+y^2+z^2)^(5/2) Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)])},{(x z Sqrt[(x^2+y^2)/(x^2+y^2+z^2)] ((x^2+y^2+z^2)^(5/2) \[Beta]^2+M^2 Sqrt[x^2+y^2+z^2] \[Alpha] (-3+\[Beta]^2)-M (x^2+y^2+z^2)^2 (-3+2 \[Beta]^2)))/(Sqrt[x^2+y^2] (x^2+y^2+z^2)^(5/2) Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)]),(y z Sqrt[(x^2+y^2)/(x^2+y^2+z^2)] ((x^2+y^2+z^2)^(5/2) \[Beta]^2+M^2 Sqrt[x^2+y^2+z^2] \[Alpha] (-3+\[Beta]^2)-M (x^2+y^2+z^2)^2 (-3+2 \[Beta]^2)))/(Sqrt[x^2+y^2] (x^2+y^2+z^2)^(5/2) Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)]),-((Sqrt[(x^2+y^2+z^2)^2 \[Beta]^2+M (-2 (x^2+y^2+z^2)^(3/2)+M \[Alpha]) (-1+\[Beta]^2)] ((x^2+y^2) (x^2+y^2+z^2)^2 \[Beta]^2+M^2 \[Alpha] (2 z^2+x^2 (-1+\[Beta]^2)+y^2 (-1+\[Beta]^2))-M (x^2+y^2+z^2)^(3/2) (z^2+2 x^2 (-1+\[Beta]^2)+2 y^2 (-1+\[Beta]^2))))/((x^2+y^2+z^2)^(9/2) \[Beta]^2-2 M (x^2+y^2+z^2)^4 (-1+\[Beta]^2)+M^2 (x^2+y^2+z^2)^(5/2) \[Alpha] (-1+\[Beta]^2)))}}


toRegularTrig[trigcoor_]:=Block[{v1={0,0},v2={1,0},v3={1/2,Sqrt[3]/2},transvec,newCoor,matrix,a,eqs,sol},
transvec=trigcoor//First;
newCoor=#-transvec&/@trigcoor;
newCoor=ReplacePart[newCoor,1->{0,0}];
matrix=Table[a[x,y],{x,1,2},{y,1,2}];
eqs=matrix.#&/@newCoor//Rest;
eqs=MapThread[Thread[#1==#2]&,{eqs,{v2,v3}}]//Flatten;
sol=Solve[eqs,matrix//Flatten]//Flatten;
matrix=matrix/.sol;
{transvec,matrix,matrix.#&/@newCoor}
]


getLinearHyperSurfaceMeasure[metric_Function,verticesCoor_,xcoorHead_,prioriCoorOfSurface_:{}]:=Block[{coe,dim,coDim,coorm,metricValue,coem,equs,sol,variables,surfaceEqus,notSurfaceCoor,surfaceCoor,surfaceEqusInItsCoor,projectionMatrix,reducedMetric,measure},
SetAttributes[coe,NHoldAll];
dim=Length[verticesCoor//First];
coDim=Length[verticesCoor]-1;
coDim=dim-coDim;
If[coDim<0,Print["too many the vertices to give a hypersurface in the manifold"];Return[{{},{},{},{}}]];
coorm=xcoorHead/@Range[dim];
metricValue=metric@@coorm;
If[coDim==0,Return[{Sqrt[Abs[Det[metricValue]]],coorm,coorm,{}}]];
coem=Tuples[{Range[coDim],Range[dim+1]}];
coem=coe@@@coem;
coem=GroupBy[coem,First]//Values;
equs=Prepend[#,1]&/@verticesCoor;
equs=Function[u,(u.#)&/@equs]/@coem;
equs=equs//Flatten;
equs=equs==0//Thread;
variables=coem//Flatten;
sol=FindInstance[equs,variables,Reals,3];
sol=FirstCase[sol,_?(Chop[Norm[variables]/.#,10^-4]!=0&)];
If[sol===Missing["NotFound"],sol=FindInstance[{equs,Norm[variables]>1}//Flatten,variables,Reals]];
surfaceEqus=#.Flatten[{1,coorm}]&/@coem;
surfaceEqus=surfaceEqus/.sol;
notSurfaceCoor=Complement[coorm,prioriCoorOfSurface];
notSurfaceCoor=Subsets[notSurfaceCoor,{coDim}];
notSurfaceCoor=FirstCase[notSurfaceCoor,_?(Length[CoefficientArrays[surfaceEqus,#]]==2&& (Det[CoefficientArrays[surfaceEqus,#]//Last//Normal]//Chop)!=0&)];
If[notSurfaceCoor===Missing["NotFound"],Print["the preferred hypersurface coordinate is not a good choice"];Return[{{},{},{},{}}]
];
surfaceCoor=Complement[coorm,notSurfaceCoor];
surfaceEqusInItsCoor=Solve[surfaceEqus==0//Thread,notSurfaceCoor]//Flatten;
projectionMatrix=coorm/.surfaceEqusInItsCoor;
projectionMatrix=D[projectionMatrix,{surfaceCoor}];
reducedMetric=Transpose[projectionMatrix].metricValue.projectionMatrix;
measure=Sqrt[Abs[Det[reducedMetric]]]/.surfaceEqusInItsCoor;
{measure,surfaceCoor,surfaceEqusInItsCoor,coorm}
]


trigAreaInCurvedGeometry[metric_Function,trigsCoor_]:=Block[{xcoor,measure,coorOfTrig,trigEqus,coorm,regionCoor,coorTransVec,coorTransMatrix,region,changeCoorRule,x,y,jacobian,area},
SetAttributes[xcoor,NHoldAll];
{measure,coorOfTrig,trigEqus,coorm}=getLinearHyperSurfaceMeasure[metric,trigsCoor,xcoor];
regionCoor=Thread[coorm->#]&/@trigsCoor;
regionCoor=coorOfTrig/.regionCoor;
{coorTransVec,coorTransMatrix,regionCoor}=toRegularTrig[regionCoor];
region=MeshRegion[regionCoor,Triangle[{1,2,3}]];
changeCoorRule=coorOfTrig->(Inverse[coorTransMatrix].{x,y}+coorTransVec)//Thread;
measure=measure/.changeCoorRule;
jacobian=Det[Inverse[coorTransMatrix]]//Abs;
area=NIntegrate[measure,{x,y}\[Element]region,WorkingPrecision->10];
area=area jacobian
]


toRegularTetrahedron[tetracoor_]:=Block[{v1={0,0,0},v2={-(Sqrt[3]/2),1/2,0},v3={-(Sqrt[3]/2),-(1/2),0},v4={-(1/Sqrt[3]),0,Sqrt[2/3]},transvec,newCoor,matrix,a,eqs,sol},
transvec=tetracoor//First;
newCoor=#-transvec&/@tetracoor;
newCoor=ReplacePart[newCoor,1->{0,0,0}];
matrix=Table[a[x,y],{x,1,3},{y,1,3}];
eqs=matrix.#&/@newCoor//Rest;
eqs=MapThread[Thread[#1==#2]&,{eqs,{v2,v3,v4}}]//Flatten;
sol=Solve[eqs,matrix//Flatten]//Flatten;
matrix=matrix/.sol;
{transvec,matrix,matrix.#&/@newCoor}
]


(*we need to give the foliation of the tetrahedron (p1,p2,p3,p4) bounded by regionCoor with (p1,p2,p3) on xy-plane, and the intersection of the line connecting lineIntersectingXYPlane and p4 with each slice in the foliation*)
foliation[regionCoor_,lineIntersectingXYPlane_,nsurfaces_,delta_]:=Block[{zcoors,surfaces,surfaceSol0,zp,p1,p2,t,xp,yp,surfaceSol1,intersection},
zcoors=regionCoor[[-1,-1]];
zcoors=Range[0,1,1/nsurfaces](zcoors-delta);
(*here we only foliate z in [0,zcoors-delta]*)
surfaces=zp-#==0&/@zcoors;
p1=regionCoor[[-1]];
p2=regionCoor[[1;;-2]];
surfaceSol0=Most/@p2;
surfaceSol1=Table[{xp,yp}/.First[NSolve[{{xp,yp,zp}==t*p1+(1-t) #,surfaces[[i]],0<t<=1},{t,xp,yp,zp}]]&/@p2,{i,2,Length[surfaces]}];
surfaceSol1=Prepend[surfaceSol1,surfaceSol0];
surfaceSol1=zcoors->(MeshRegion[#,Triangle[{1,2,3}]]&/@surfaceSol1)//Thread;
intersection=(NSolve[{{xp,yp,zp}==(1-t)lineIntersectingXYPlane+t  p1,#},{t,xp,yp,zp}]//First)&/@surfaces;
intersection=({xp,yp,zp})/.intersection;
{surfaceSol1,intersection}
]


intKAlongLink[extrinsicKUpperFun:{extrinsicKUpperFun4Tetra1_Function,extrinsicKUpperFun4Tetra2_Function},metricFuns_,tetrahedraCoor_,SharedTrigCoor_,numOfFoliation_:100]:=Block[{xcoor,coorm,extrinsicKUpper,metric,centroidCoor,regionCoor,linePlaneIntersection,t,t1,t2,transVec,transMatrix,coorChange,x,y,z,stepFun2Greaterrb,inverseMetric,surfaces,intersectingCoor,surfaceCoNormal,surfaceNormal,surfaceVolumeElement,area,indexa,Knn4Int,averageK,linkTangent,lengthLinkTangent,rule4intersectingCoor,averageK4LinkInt,intK},
SetAttributes[xcoor,NHoldAll];
coorm={xcoor/@Range[3],xcoor/@Range[3]};
extrinsicKUpper=MapThread[#1@@#2&,{extrinsicKUpperFun,coorm}];
metric=MapThread[#1@@#2&,{metricFuns,coorm}];
centroidCoor=(Total[#]/4)&/@tetrahedraCoor;
regionCoor=Append[SharedTrigCoor,#]&/@centroidCoor;
linePlaneIntersection=NSolve[SharedTrigCoor[[1]](1-t1-t2)+t1 SharedTrigCoor[[2]]+t2 SharedTrigCoor[[3]]==centroidCoor[[1]](1-t)+t centroidCoor[[2]],{t1,t2,t}]//First;
linePlaneIntersection=centroidCoor[[1]]+t(centroidCoor[[2]]-centroidCoor[[1]])/.linePlaneIntersection;
{transVec,transMatrix,regionCoor}=toRegularTetrahedron/@regionCoor//Transpose;
linePlaneIntersection=MapThread[#1.(linePlaneIntersection-#2)&,{transMatrix,transVec}];
transMatrix=Inverse/@transMatrix;
coorChange=MapThread[#1.{x,y,z}+#2&,{transMatrix,transVec}];
coorChange=MapThread[(Rule[#1,#2]//Thread)&,{coorm,coorChange}];
stepFun2Greaterrb=HeavisideTheta[#.#-rb^2]&/@coorm;
stepFun2Greaterrb=MapThread[#1/.#2&,{stepFun2Greaterrb,coorChange}];
extrinsicKUpper=MapThread[Inverse[#2].#1.Transpose[Inverse[#2]]&,{extrinsicKUpper,transMatrix}];
extrinsicKUpper=MapThread[#1/.#2&,{extrinsicKUpper,coorChange}];
metric=MapThread[Transpose[#1].#2.#1&,{transMatrix,metric}];
metric=MapThread[#1/.#2&,{metric,coorChange}];
inverseMetric=Inverse/@metric;{surfaces,intersectingCoor}=MapThread[foliation[#1,#2,numOfFoliation,1/1000]&,{regionCoor,linePlaneIntersection}]//Transpose;
surfaceCoNormal={{0,0,1},{0,0,1}};
surfaceCoNormal=MapThread[#1/Sqrt[#1.#2.#1]&,{surfaceCoNormal,inverseMetric}];
surfaceNormal=MapThread[#1.#2&,{inverseMetric,surfaceCoNormal}];
surfaceVolumeElement=MapThread[Sqrt[Det[#1]]#2.{0,0,1}&,{metric,surfaceNormal}];
Knn4Int=MapThread[(#1.#2.#1)#3&,{surfaceCoNormal,extrinsicKUpper,surfaceVolumeElement}];
area=Table[ParallelMap[NIntegrate[(surfaceVolumeElement[[indexa]]stepFun2Greaterrb[[indexa]] )/.z->#[[1]],{x,y}\[Element]#[[2]]]&,surfaces[[indexa]]],{indexa,{1,2}}];
(*here Re[Knn4Int] is just Knn4Int times the step function*)
averageK=Table[ParallelMap[NIntegrate[(Knn4Int[[indexa]]//Re)/.z->#[[1]],{x,y}\[Element]#[[2]]]&,surfaces[[indexa]]],{indexa,{1,2}}];
averageK=averageK/area;
linkTangent=MapThread[#1-#2&,{regionCoor[[All,-1]],linePlaneIntersection}];
linkTangent=#/#[[3]]&/@linkTangent;(*so that ds=Sqrt[tangent.q.tangent]dz*)
lengthLinkTangent=MapThread[Sqrt[#1.#2.#1]&,{linkTangent,metric}];
rule4intersectingCoor=Map[Thread[{x,y,z}->#]&,intersectingCoor,{2}];
lengthLinkTangent=MapThread[#1/.#2&,{lengthLinkTangent,rule4intersectingCoor}];
averageK4LinkInt=averageK lengthLinkTangent;
averageK4LinkInt=Transpose/@({Keys/@surfaces,averageK4LinkInt}//Transpose);
averageK4LinkInt=Interpolation/@averageK4LinkInt;
intK=NIntegrate[#[x],{x,#["Domain"][[1,1]],#["Domain"][[1,2]]}]&/@averageK4LinkInt;
intK=Total[intK]
]


dihedralAnglesface[{Na_,Nb_}]/;Na.eta.Na>0&&Nb.eta.Nb>0&&Abs[Na.eta.Nb]<1:=Block[{Na2,Nb2,Nab},Na2=Na.eta.Na;Nb2=Nb.eta.Nb;
If[Na2>0&&Nb2>0,Pi-ArcCos[Na.eta.Nb],"Not timelike face"]]
dihedralAnglesface[{Na_,Nb_}]:=Block[{Na2,Nb2,Nab},Na2=Na.eta.Na;Nb2=Nb.eta.Nb;
Nab=Na.eta.Nb;
Which[Na2>0&&Nb2>0,If[Nab>0,ArcCosh[Na.eta.Nb],-ArcCosh[-Na.eta.Nb]],Na2*Nb2<0,ArcSinh[Na.eta.Nb],Na2<0&&Nb2<0,If[Nab<0,-ArcCosh[-Na.eta.Nb],ArcCosh[Na.eta.Nb]]]]
dihedralAngleInFlatGeometry[tetrahedronInSimplex_Rule,ruleLabelVertex_]:=Block[{coor,normals,ingoingvec,sign,dihedralAngles},
coor=MapIndexed[Function[u,{List@@u,Complement[List@@(#2//First//First),List@@u]//First}]/@#1&,tetrahedronInSimplex//Association];
coor=(#/.ruleLabelVertex)&/@coor;
normals=(First/@#)&/@coor//Values//First;
normals=getTetrahedronNormal/@normals;
ingoingvec=Last/@#&/@coor;
ingoingvec=MapIndexed[Function[u,{u,(Plus@@(#2//First//First))/5}]/@#1&,ingoingvec]//Values//First;
ingoingvec=ingoingvec/.ruleLabelVertex;
ingoingvec=#[[1]]-#[[2]]&/@ingoingvec;
sign=MapThread[#1.eta.#2&,{normals,ingoingvec}];
sign=Sign/@sign;
normals=normals sign;
dihedralAnglesface[normals]
]
dihedralAngleInFlatGeometry[tetrahedronInSimplex:{_Rule...},ruleLabelVertex_]:=(dihedralAngleInFlatGeometry[#,ruleLabelVertex]&/@tetrahedronInSimplex)//Total
