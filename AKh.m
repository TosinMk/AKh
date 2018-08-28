(* ::Package:: *)

BeginPackage["AKh`", "KnotTheory`"]

NumberOfCrossings::usage = "Determines the number of crossings in a planar diagram."
NumberOfNegativeCrossings::usage = "Counts the number of negative crossings."
NumberOfPositiveCrossings::usage = "Counts the number of positive crossings."

Smoothings::usage = "The set of smoothings for a given planar diagaram."
Circles::usage = "Returns the circles for a given smoothing of a planar diagram."
CubeOfCircles::usage = "Complete set of smoothings of a planar diagram."
SortCircles::usage ="Determines whether a circle is homologically trivial in the annulus or not."

QuantumDegree::usage = "Calculates the quantum degree of a given basis element."
AnnularDegree::usage = "Calculates the annular degree of a given basis element."
V::usage = "The vector space attached to a given smoothing."
d::usage = "Khovanov's differential is modified to preserve annular grading. 
			There are three possibilities: 
			1) Two homologically trivial cycles merge to another homologically trivial cycle
			2) One trivial cycle and one non-trivial cycle merge to a non-trivial cycle
			3) Two non-trivial cycles merge to a trivial cycle
			And the same holds for the split map."

KhBracket::usage = "Finds the i-th group in the Khovanov bracket chain complex by direct 
					summing all the vector spaces of height i."
CC::usage = "Shifts the Khovanov bracket." 
differential::usage = "Calculates the differential applied to a basis element."

Rank::usage = "Calculates dimension of Im(differential)"

Betti::usage = "The dimension of the homogeneous component of AKh with fixed quantum and 
				annular gradings."
qtBetti::usage = "Sums Betti over all possible pairings of quantum and annular gradings."
AKh::usgae = "The Poincar\[EAcute] polynomial for the annular Khovanov homology."

AKhTable::usage = "Outputs the dimensions of the Poincar\[EAcute] polynomial in table form."



q
t
n
v
vm
vp
s

Begin["Private`"]

NumberOfCrossings[L_PD] := Count[L, X[i_,j_,k_,l_]]
NumberOfPositiveCrossings[L_PD] := Count[L, X[i_,j_,k_,l_] /; j-l==1 || l-j>1]
NumberOfNegativeCrossings[L_PD] := Count[L, X[i_,j_,k_,l_] /; l-j==1 || j-l>1]

Smoothings[L_PD] := Module[{length, types}, length = NumberOfCrossings[L]; types = Tuples[{0,1}, length]]

Circles[L_PD, a : {(0|1)...}] := Module[{i,j,k,l},ConnectedComponents[Graph[DeleteDuplicates[Flatten[(Thread[{List @@ L,a}] /. { {X[i_,j_,k_,l_],0} -> {{i,j},{k,l}}, {X[i_,j_,k_,l_],1} -> {{i,l},{j,k}} }),1], SameQ[#1,#2]||SameQ[#1,Reverse@#2]&]]]]
 Circles[L_PD, a_List] := Module[{list}, list =Thread[{List @@ L, a}]; Circles[L,a /. {"*" -> 0}] -> Circles[L, a /. {"*" -> 1}]]

CubeOfCircles[L_PD] := Module[{types}, types = Smoothings[L]; Circles[L,#] &/@types]

SortCircles[b_List, c_List] := Times @@ Table[If[Mod[Length[Intersection[b[[n]],c]],2]==0, trivial[Min[b[[n]]]], nontrivial[Min[b[[n]]]]],{n, Length[b]}]
SortCircles[expr_, c_List] := SortCircles[DeleteCases[expr[[1]], Alternatives @@ Intersection[expr[[1]],expr[[2]]  ]  ], c] -> SortCircles[DeleteCases[expr[[2]], Alternatives @@ Intersection[expr[[1]],expr[[2]]  ]  ],c] 

QuantumDegree[expr_] := Count[expr, _vp, {0,1}] - Count[expr, _vm, {0,1}]

AnnularDegree[expr_] := Count[expr, vp[_,n], {0,1}] - Count[expr, vm[_,n], {0,1}] 

V[L_PD, a_List, c_List] := List @@ Expand[SortCircles[Circles[L,a], c] /. {trivial[x_] -> ((vp[x,t])+(vm[x,t])), nontrivial[x_] -> ((vp[x,n])+(vm[x,n])) } ] 
V[L_PD, a_List,c_List, deg_Integer, deg2_Integer] := Select[V[L,a,c], ((deg == QuantumDegree[#] + (Plus @@ a)) && (deg2 == AnnularDegree[#])) & ]

d[L_PD, a_List, b_List] := SortCircles[Circles[L, a],b] /. {  
(trivial[x_]trivial[y_] -> trivial[z_]) -> {vp[x,t]vp[y,t] -> vp[z,t], vp[x,t]vm[y,t] -> vm[z,t], vm[x,t]vp[y,t] -> vm[z,t], vm[x,t]vm[y,t] -> 0}, 
(trivial[z_] -> trivial[x_]trivial[y_]) -> {vp[z,t] -> vp[x,t]vm[y,t] + vm[x,t]vp[y,t], vm[z,t] -> vm[x,t]vm[y,t]}, 
(trivial[x_]nontrivial[y_] -> nontrivial[z_]) -> {vp[x,t]vm[y,n] -> vm[z,n], vm[x,t]vp[y,n] -> 0, vp[x,t]vp[y,n] -> vp[z,n], vm[x,t]vm[y,n] -> 0}, 
(nontrivial[z_] -> trivial[x_]nontrivial[y_]) -> {vp[z,n] -> vm[x,t]vp[y,n], vm[z,n] -> vm[x,t]vm[y,n]}, 
(nontrivial[x_]nontrivial[y_] -> trivial[z_]) -> {vp[x,n]vm[y,n] -> vm[z,t], vm[x,n]vp[y,n] -> vm[z,t], vp[x,n]vp[y,n] -> 0, vm[x,n]vm[y,n] -> 0}, 
(trivial[z_] -> nontrivial[x_]nontrivial[y_]) -> {vp[z,t] -> vp[x,n]vm[y,n] + vm[x,n]vp[y,n], vm[z,t] -> 0}
}

KhBracket[L_PD, c_List, r_Integer, deg___, deg2___] := 
If[r<0||r>Length[L], {0}, Join @@ 
(((v[#])V[L, #,c, deg, deg2]) & /@ Permutations[Join[Table[0, {Length[L]-r}], Table[1,{r}]]])]

CC[L_PD, c_List, r_Integer, deg_Integer, deg2_Integer] := 
KhBracket[L, c, r + NumberOfNegativeCrossings[L], deg - NumberOfPositiveCrossings[L] + 2 NumberOfNegativeCrossings[L], deg2 ]

ReplaceHead[expr_] := 
Expand[ sign=1; Table[   If[ expr[[1,1,i]]==0, sign ReplacePart[expr, {1,1,i} ->  1],sign=-1 sign;0] ,{i, Length[expr[[1,1]] ] } ] ]

ReplaceBody[L_PD, b_List][expr_] :=   
d[L, #, b]  & /@ Table[ ReplacePart[expr, {1,1,i} -> "*"][[1,1]],{i,1,Length[(expr)[[1,1]] ]}] 

differential[L_PD, b_List][expr_] := Module[ {ReplaceOne, ReplaceStar}, ReplaceOne = ReplaceHead[expr]; ReplaceStar = ReplaceBody[L,b][expr]; Total[MapThread[#1 /. #2 &, {ReplaceOne, ReplaceStar} ] ] ]
differential[L_PD, b_List][0] := 0

Options[Betti] = {Modulus -> Infinity}
Rank[L_PD,a_List, r_Integer, deg_Integer, deg2_Integer, opts___] := (
modulus = If[{opts} === {}, Modulus /. Options[Betti], Modulus /. {opts}];
Off[Solve::svars];
b0 = CC[L, a, r, deg, deg2];
L1 = Length[b1 = CC[L, a, r+1, deg, deg2]];
equations = (#==0) & /@ (Expand[differential[L, a][#] &/@ b0 ]  /. MapThread[Rule, {b1, variables=Array[b,L1]}] );
rk = Which[b0 === {0} || b1 === {0}, 0,b0=== {} || b1==={},0, modulus === Infinity, MatrixRank[Normal[CoefficientArrays[equations, variables]][[2]] ] ,
modulus =!= Infinity, MatrixRank[Normal[CoefficientArrays[equations, variables]][[2]] , Modulus -> modulus]
];
On[Solve::svars];
rk 
)
 
Betti[L_PD, a_List, r_Integer, deg_Integer, deg2_Integer, opts___] := 
Module[{z}, 
	z= If[ CC[L,a,r,deg,deg2] === {0} || CC[L,a,r,deg,deg2] === {}, 0, Length[ CC[L,a,r,deg,deg2] ] - Rank[L,a,r,deg,deg2,opts] - Rank[L,a,r-1,deg,deg2,opts] ];
Print[StringForm[ "Betti[``,``,``] = ``",r,deg,deg2,z]];z]

qtBetti[L_PD, a_List, r_Integer, opts___] := 
(qdegs = 
	If[KhBracket[L, a, r + NumberOfNegativeCrossings[L]] === {0}, 0, Union[QuantumDegree /@ KhBracket[L, a, r + NumberOfNegativeCrossings[L]] + NumberOfPositiveCrossings[L] -NumberOfNegativeCrossings[L] + r] ]; 
tdegs = 
	If[KhBracket[L, a, r + NumberOfNegativeCrossings[L]] === {0}, 0, Union[AnnularDegree /@ KhBracket[L, a, r + NumberOfNegativeCrossings[L]]] ];
(Flatten[Outer[Betti[L, a, r, #1, #2, opts](q^#1 )(t^#2) &, {qdegs}, {tdegs}],3]) )

AKh[L_PD, a_List, opts___] := Expand[Sum[Total[s^r  qtBetti[L,a,r,opts]], {r, -NumberOfNegativeCrossings[L], Length[L] - NumberOfNegativeCrossings[L] } ] ] 

KhTable[kh_]:=                      
Module[{poly=kh,qShift,tShift,gridPoly,body,head},
qShift = -(Exponent[poly,q,Min]);tShift = -(Exponent[poly,s,Min]);
gridPoly = Expand[poly*(q^qShift)*(s^tShift)];
body = CoefficientList[gridPoly, {q,s}];
head = {Table[i, {i,-qShift, Exponent[poly,q,Max]}], Table[i, {i,-tShift, Exponent[poly,s,Max]}]};
Grid[Prepend[Flatten/@Transpose[{head[[1]],body}],PadLeft[head[[2]],Length@body[[1]]+1,""]], Frame -> All]
] 

condense[table_]:=  
Module[{t = table,n,min,eTable,head},
n = t[[1,-1,1]]/2;
min = t[[1,2,1]];
If[min<=0, n++;
n += Abs[min]/2];
eTable = Table[t[[1,2i]], {i,1,n}];
head = Range[t[[1,1,2]],t[[1,1,-1]]];
PrependTo[head,"q\[Backslash]s"];
PrependTo[eTable,head];
Grid[eTable, Frame -> All] ]

AKhTable[L_PD, a_List, opts___] := condense[KhTable[SKh[L, a, opts]]]

End[]
EndPackage[]

