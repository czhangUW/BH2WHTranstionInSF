(* ::Package:: *)

fixSL2CGauge[{allTetrahedraInSimplex_Association,unFixedv_,fixedve_,otherForbiddenve_,prioriChoose4GaugeFix_}]:=Block[{whichToFix,gaugefixve},
whichToFix={unFixedv,unFixedv/.allTetrahedraInSimplex}//Transpose;
whichToFix=Thread/@whichToFix;
whichToFix=DeleteCases[#,_?(MemberQ[otherForbiddenve,#]&)]&/@whichToFix;
whichToFix=DeleteCases[#,_?(IntersectingQ[#,fixedve//Flatten]&)]&/@whichToFix;
whichToFix=SortBy[whichToFix,Length];
whichToFix=whichToFix//First;
gaugefixve=FirstCase[whichToFix,_?(MemberQ[prioriChoose4GaugeFix,#]&)];
If[gaugefixve==Missing["NotFound"],gaugefixve=whichToFix//First];
{allTetrahedraInSimplex,DeleteCases[unFixedv,gaugefixve//First],Append[fixedve,gaugefixve],otherForbiddenve,prioriChoose4GaugeFix}
]


getComplexCriticalPoint[ruleLabelVertexCurvedGeometryp_,deltaLrule_,simplicesInLabel_,bdyTetrahedrap_,sl2cGaugeFixTetr_,SU2GaugeFixve_,initialRule_,workingprecise_,if4DoubleRegion_,immiriziValue_:1]:=Block[{ruleLabelVertexCurvedGeometry,curvedSFData,assignG0Rule,assignG0DaggerRule,sl2cRules4CC,sl2cVariables,assignZ0Rule,assignZ0GaugeRule,assignZ0DaggerRule,spinorRules4CC,areafRule,areaVariables,spinorVariables,alleqs,allvariables,sol,checkSol,totalAction},
ruleLabelVertexCurvedGeometry=ruleLabelVertexCurvedGeometryp/.deltaLrule;
curvedSFData=getSFDataFromCurvedComplex[ruleLabelVertexCurvedGeometry,simplicesInLabel,bdyTetrahedrap];
assignG0Rule=Cases[curvedSFData[[1]]//Normal,HoldPattern[{_Simplex,_Tetrahedron}->_]]//Association;
assignG0DaggerRule=ConjugateTranspose/@assignG0Rule;
{sl2cRules4CC,sl2cVariables}=getSL2CRules[assignG0Rule,assignG0DaggerRule,myConjugateTranspose,sl2cGaugeFixTetr,SU2GaugeFixve];
{assignZ0Rule,assignZ0GaugeRule}=getSpinor0RuleFromSFData[curvedSFData[[4]],curvedSFData[[1]]];
assignZ0DaggerRule=Conjugate/@assignZ0Rule;
{spinorRules4CC,spinorVariables}=getSpinorRule[assignZ0Rule,assignZ0DaggerRule,assignZ0GaugeRule,myConjugate];
{areafRule,areaVariables}=getAreaRule[curvedSFData[[4]],curvedSFData[[2]]];
totalAction=actionTotal[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4CC,spinorRules4CC,areafRule];
totalAction=totalAction/.Immirzi->immiriziValue//N[#,precise]&;
allvariables={areaVariables["internal"],sl2cVariables,spinorVariables}//Flatten;
alleqs=D[totalAction,#]&/@allvariables;
allvariables=If[initialRule==={},{#,0}&/@allvariables,{allvariables,allvariables/.initialRule}//Transpose];
sol=FindRoot[alleqs,allvariables,WorkingPrecision->workingprecise];
sol=Dispatch[sol];
checkSol=alleqs/.sol//Chop[#,10^-chopdelta]&//AllTrue[#,#==0&]&;
If[!checkSol,Return["solution is not good"]];
(*here we calculate totalAction again to get expression with Immirzi*)
totalAction=actionTotal[curvedSFData[[4]],curvedSFData[[3]],"spacelike",sl2cRules4CC,spinorRules4CC,areafRule];
totalAction=totalAction/.sol//Expand;
If[!if4DoubleRegion,Return[{sol,totalAction}]];
{sol,totalAction,sl2cGaugeFixTetr,SU2GaugeFixve,curvedSFData,sl2cRules4CC,spinorRules4CC,areafRule,assignZ0GaugeRule}
]
