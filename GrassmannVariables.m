(* ::Package:: *)

version=1.0;
Print["Grassmann variables ",ToString@NumberForm[version,{20,1}]]
Print["by Alexander G Tumanov"]

Clear[FF]
FF[a___] := Signature[List@a]FF@@Sort[List@a]/;!OrderedQ[List@a]
FF[a___] := 0/;Length@Union[List@a]<Length[List@a]
FF[a___] := 0/;MemberQ[List@a,0]
FF[] := 1

Clear[CircleTimes]
a_\[CircleTimes]b_ := 
	Block[{AA=Collect[a,FF[___]],BB=Collect[b,FF[___]]},
		AA = If[TrueQ[Head@AA==Plus],List@@AA,{AA}];
		BB = If[TrueQ[Head@BB==Plus],List@@BB,{BB}];
		Sum[If[Length[Cases[{AA[[pp]],BB[[qq]]},FF[___],\[Infinity]]]<=1,AA[[pp]]BB[[qq]],(AA[[pp]]BB[[qq]]/.FF[___]->1)(FF@@Join[List@@(Cases[{AA[[pp]]},FF[___],\[Infinity]][[1]]), List@@(Cases[{BB[[qq]]},FF[___],\[Infinity]][[1]])])],{pp,Length[AA]},{qq,Length[BB]}]
	]/;!ListQ[a]&&!ListQ[b]
a_\[CircleTimes]b_ := a\[CircleTimes]#& /@ b /;!ListQ[a]&&ListQ[b]
a_\[CircleTimes]b_ := #\[CircleTimes]b& /@ a /;ListQ[a]&&!ListQ[b]
CircleTimes[a_, b_, c__] := a\[CircleTimes](b\[CircleTimes]c)

Clear[ParallelCircleTimes]
ParallelCircleTimes[a_, b_] := 
	Block[{AA=Collect[a,FF[___]],BB=Collect[b,FF[___]],index},
		AA = If[TrueQ[Head@AA==Plus],List@@AA,{AA}];
		BB = If[TrueQ[Head@BB==Plus],List@@BB,{BB}];
		index = Flatten@Table[ind[pp,qq],{pp,Length[AA]},{qq,Length[BB]}]/.ind->List;
		ParallelSum[If[Length[Cases[{AA[[index[[ii,1]]]],BB[[index[[ii,2]]]]},FF[___],\[Infinity]]]<=1,AA[[index[[ii,1]]]]BB[[index[[ii,2]]]],(AA[[index[[ii,1]]]]BB[[index[[ii,2]]]]/.FF[___]->1)(FF@@Join[List@@(Cases[{AA[[index[[ii,1]]]]},FF[___],\[Infinity]][[1]]),List@@(Cases[{BB[[index[[ii,2]]]]},FF[___],\[Infinity]][[1]])])],{ii,Length[index]}]
	]/;!ListQ[a]&&!ListQ[b]
ParallelCircleTimes[a_, b_] := ParallelCircleTimes[a,#]& /@ b /;!ListQ[a]&&ListQ[b]
ParallelCircleTimes[a_, b_] := ParallelCircleTimes[#,b]& /@ a /;ListQ[a]&&!ListQ[b]
ParallelCircleTimes[a_,b_,c__] := ParallelCircleTimes[a,ParallelCircleTimes[b,c]]

Clear[GDot]
GDot[a_, b_] := Expand@Table[Sum[a[[pp,kk]]\[CircleTimes]b[[kk,qq]],{kk,Length[b]}],{pp,Length[a]},{qq,Length[b[[1]]]}]/;MatrixQ[a]&&MatrixQ[b]&&TrueQ[Length[a[[1]]]==Length[b]]
GDot[a_, b_] := Expand@Table[Sum[a[[pp,kk]]\[CircleTimes]b[[kk]],{kk,Length[b]}],{pp,Length[a]}]/;MatrixQ[a]&&VectorQ[b]&&TrueQ[Length[a[[1]]]==Length[b]]
GDot[a_, b_] := Expand@Table[Sum[a[[kk]]\[CircleTimes]b[[kk,qq]],{kk,Length[b]}],{qq,Length[b[[1]]]}]/;VectorQ[a]&&MatrixQ[b]&&TrueQ[Length[a]==Length[b]]
GDot[a_, b_] := Expand@Sum[a[[kk]]\[CircleTimes]b[[kk]],{kk,Length[b]}]/;VectorQ[a]&&VectorQ[b]&&TrueQ[Length[a]==Length[b]]
GDot[a_, b_, c__] := GDot[a,GDot[b,c]]

Clear[GIntegrate]
GIntegrate[a_, \[Theta]_, norm_] := (a/.FF->FFreplaced/.FFreplaced[AA___,\[Theta],BB___]:>norm (-1)^Length[{AA}] FF[AA,BB]/.FFreplaced[___]:>0)-(a/.FF[___]:>0)/;!ListQ[a]&&!ListQ[\[Theta]]
GIntegrate[a_, \[Theta]_, norm_] := GIntegrate[#,\[Theta]]&/@a/;VectorQ[a]&&!ListQ[\[Theta]]
GIntegrate[a_, \[Theta]_, norm_] := Block[{output=a},Do[output=GIntegrate[output,\[Theta][[Length[\[Theta]]-kk+1]],norm],{kk,Length[\[Theta]]}];output]/;!ListQ[a]&&VectorQ[\[Theta]]
GIntegrate[a_, \[Theta]_, norm_] := GIntegrate[#,\[Theta]]&/@a/;VectorQ[a]&&VectorQ[\[Theta]]
GIntegrate[a_, \[Theta]_] := GIntegrate[a,\[Theta],1]

Clear[GExp]
GExp[a_] :=
	Block[{AA=a/.FF[___]->0,BB=a-(a/.FF[___]->0),CC=a-(a/.FF[___]->0),DD=1,pp=1},
		While[!FreeQ[CC,FF[___]],DD=DD+CC;pp=pp+1;CC=(CC\[CircleTimes]BB)/pp];
		Exp@Expand[AA]Expand[DD]
	]/;!ListQ[a]
