(* ::Package:: *)

version=1.0;
Print["Grassmann variables ",version]
Print["by Alexander G Tumanov"]

Clear[FF]
FF[a___]:=Signature[List@a]FF@@Sort[List@a]/;!OrderedQ[List@a]
FF[a___]:=0/;Length@Union[List@a]<Length[List@a]
FF[a___]:=0/;MemberQ[List@a,0]
FF[]:=1

Clear[CircleTimes,GDot]
a_\[CircleTimes]b_:=Block[{AA=Collect[a,FF[___]],BB=Collect[b,FF[___]]},AA=If[TrueQ[Head@AA==Plus],List@@AA,{AA}];BB=If[TrueQ[Head@BB==Plus],List@@BB,{BB}];Sum[If[Length[Cases[{AA[[pp]],BB[[qq]]},FF[___],\[Infinity]]]<=1,AA[[pp]]BB[[qq]],(AA[[pp]]BB[[qq]]/.FF[___]->1)(FF@@Join[List@@(Cases[{AA[[pp]]},FF[___],\[Infinity]][[1]]),List@@(Cases[{BB[[qq]]},FF[___],\[Infinity]][[1]])])],{pp,Length[AA]},{qq,Length[BB]}]]/;!ListQ[a]&&!ListQ[b]
a_\[CircleTimes]b_:=a\[CircleTimes]#&/@b/;!ListQ[a]&&ListQ[b]
a_\[CircleTimes]b_:=#\[CircleTimes]b&/@a/;ListQ[a]&&!ListQ[b]
CircleTimes[a_,b_,c__]:=a\[CircleTimes](b\[CircleTimes]c)
GDot[a_,b_]:=Expand@Table[Sum[a[[pp,kk]]\[CircleTimes]b[[kk,qq]],{kk,Length[b]}],{pp,Length[a]},{qq,Length[b[[1]]]}]/;MatrixQ[a]&&MatrixQ[b]&&TrueQ[Length[a[[1]]]==Length[b]]
GDot[a_,b_]:=Expand@Table[Sum[a[[pp,kk]]\[CircleTimes]b[[kk]],{kk,Length[b]}],{pp,Length[a]}]/;MatrixQ[a]&&VectorQ[b]&&TrueQ[Length[a[[1]]]==Length[b]]
GDot[a_,b_]:=Expand@Table[Sum[a[[kk]]\[CircleTimes]b[[kk,qq]],{kk,Length[b]}],{qq,Length[b[[1]]]}]/;VectorQ[a]&&MatrixQ[b]&&TrueQ[Length[a]==Length[b]]
GDot[a_,b_]:=Expand@Sum[a[[kk]]\[CircleTimes]b[[kk]],{kk,Length[b]}]/;VectorQ[a]&&VectorQ[b]&&TrueQ[Length[a]==Length[b]]
GDot[a_,b_,c__]:=GDot[a,GDot[b,c]]

Clear[GInt]
GInt[a_,\[Theta]_,phase_]:=(a/.FF->FFreplaced/.FFreplaced[AA___,\[Theta],BB___]:>phase (-1)^Length[{AA}] FF[AA,BB]/.FFreplaced[___]:>0)-(a/.FF[___]:>0)/;!ListQ[a]&&!ListQ[\[Theta]]
GInt[a_,\[Theta]_,phase_]:=GIntegrate[#,\[Theta]]&/@a/;VectorQ[a]&&!ListQ[\[Theta]]
GInt[a_,\[Theta]_,phase_]:=Block[{output=a},Do[output=GInt[output,\[Theta][[Length[\[Theta]]-kk+1]],phase],{kk,Length[\[Theta]]}];output]/;!ListQ[a]&&VectorQ[\[Theta]]
GInt[a_,\[Theta]_,phase_]:=GIntegrate[#,\[Theta]]&/@a/;VectorQ[a]&&VectorQ[\[Theta]]
GInt[a_,\[Theta]_]:=GInt[a,\[Theta],1]

Clear[GIntegrate,GGIntegrate]
GIntegrate[a_,phase_]:=(a/.FF->FFreplaced//.{FFreplaced[AA___,\[DoubleStruckD][aa_],BB___,aa_,CC___]:>phase (-1)^Length[{BB}] FFreplaced[AA,BB,CC],FFreplaced[AA___,aa_,BB___,\[DoubleStruckD][aa_],CC___]:>phase (-1)^(1+Length[{BB}]) FFreplaced[AA,BB,CC]}/.FFreplaced[AA___]:>0/;MemberQ[{AA},\[DoubleStruckD][___]]/.FFreplaced->FF)/;!ListQ[a]
GIntegrate[a_,phase_]:=GIntegrate[#,phase]&/@a/;ListQ[a]
GIntegrate[a_]:=GIntegrate[a,1]
GGIntegrate[a_,\[Theta]_,phase_]:=(a/.FF->FFreplaced/.{FFreplaced[AA___,\[DoubleStruckD][\[Theta]],BB___,\[Theta],CC___]:>phase (-1)^Length[{BB}] FFreplaced[AA,BB,CC],FFreplaced[AA___,\[Theta],BB___,\[DoubleStruckD][\[Theta]],CC___]:>phase (-1)^(1+Length[{BB}]) FFreplaced[AA,BB,CC]}/.FFreplaced[AA___]:>0/;MemberQ[{AA},\[DoubleStruckD][\[Theta]]]/.FFreplaced->FF)/;!ListQ[a]&&!ListQ[\[Theta]]
GGIntegrate[a_,\[Theta]_,phase_]:=(a/.FF->FFreplaced//.Flatten@Table[{FFreplaced[AA___,\[DoubleStruckD][\[Theta][[kk]]],BB___,\[Theta][[kk]],CC___]:>phase (-1)^Length[{BB}] FFreplaced[AA,BB,CC],FFreplaced[AA___,\[Theta][[kk]],BB___,\[DoubleStruckD][\[Theta][[kk]]],CC___]:>phase (-1)^(1+Length[{BB}]) FFreplaced[AA,BB,CC]},{kk,Length[\[Theta]]}]/.FFreplaced[AA___]:>0/;Or@@Table[MemberQ[{AA},\[DoubleStruckD][\[Theta][[kk]]]],{kk,Length[\[Theta]]}]/.FFreplaced->FF)/;!ListQ[a]&&VectorQ[\[Theta]]
GGIntegrate[a_,\[Theta]_,phase_]:=GGIntegrate[#,\[Theta],phase]&/@a/;ListQ[a]
GGIntegrate[a_,\[Theta]_]:=GGIntegrate[a,\[Theta],1]

Clear[GExp]
GExp[a_]:=Block[{AA=a/.FF[___]->0,BB=a-(a/.FF[___]->0),CC=a-(a/.FF[___]->0),DD=1,pp=1},While[!FreeQ[CC,FF[___]],DD=DD+CC;pp=pp+1;CC=(CC\[CircleTimes]BB)/pp];Exp@Expand[AA]Expand[DD]]/;!ListQ[a]
