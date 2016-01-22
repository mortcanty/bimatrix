(*    ============= GameTheory`Bimatrix` ================
          Algorithmic solutions for bimatrix games
                  (c) Mort Canty, 2016

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
      ===================================================
*)


BimatrixForm::usage =  "BimatrixForm[A,B] returns  the bimatrix
structure of the game {A,B}.  For display purposes only."

Bimatrix::usage   =   "Bimatrix[A,B]   returns   the   bimatrix
representation of the game with payoff matrices {A,B}."

NashEquilibria::usage = "NashEquilibria[A,B,options] returns a
list of Equilibria {{P*,I1*,Q*,I2*},...} of the bimatrix game  with
payoff matrices A and B for player 1 and 2, respectively. The
options are Algorithm, Select, and  Symbolic.  If B is  omitted
a zero-sum matrix game is assumed. If Select->ESS, a symmetric
game is assumed and B is ignored."

VE::usage =  "VE[A,B} returns  a list  of the  vertices of  the
convex polyhedron {X|A<=B,X>=0} in its first component. The
second component is a list of the corresponding cobases."

Labels::usage = "Option for BimatrixForm:
Labels->Automatic(default): Genrate automatic pure strategy labels,
Labels->List: Label pure strategies with lists provided."

Select::usage = "Option for NashEquilibria:
Select-> Automatic(default): Find Nash Equilibria of a bimatrix game,
Select-> One: Find one Nash Equilibrium,
Select-> All: Find all extreme Nash Equilibria,
Select-> AllVerbose: Find all extreme Nash Equilibria and
         print H- and V- representations and basis index sets
Select-> MNS: Find all maximal Nash subsets,
Select-> QS: Find all quasistrict extreme Nash equilibria,
Select-> ESS: Find evolutionarily stable equilibria,
Select-> Perfect: Find all perfect extreme equilibria."

Symbolic::usage = "Option for NashEquilibria.
Symbolic->Automatic(default): Payoff matrices are in numerical form,
Symbolic->List: Payoff matrices are in symbolic form, List
is a list of representative substitutions."

QS::usage = "value for Select option of NashEquilibria."
All::usage = "value for Select option of NashEquilibria."
AllVerbose = "value for Select option of NashEquilibria."
One::usage = "value for Select option of NashEquilibria."
ESS::usage = "value for Select option of NashEquilibria."
MNS::usage = "value for Select option of NashEquilibria."
Perfect::usage = "value for Select option of NashEquilibria."

Options[NashEquilibria] = {Select -> Automatic, Symbolic -> Automatic}
Options[BimatrixForm] = {Labels -> Automatic}

Verbose::usage "Option for VE:
Verbose->Automatic(default): No printed output.
Verbose->H: Print the H-representation."

Options[VE] ={Verbose -> Automatic}

Undominated::usage  =  "Undominated[P,A]  returns  True  if the
mixed strategy  P of  player 1  is not  dominated in a bimatrix
game, otherwise False.   Undominated[Q,Transpose[B] will  check
for dominance of mixed strategy Q for player 2."

$lrs::usage = "Set to False if lrs is not available";

NashEquilibria::degen = "degenerate game";
NashEquilibria::onlyone = "only one solution will be generated";


BimatrixForm[A_List,B_List,opts___Rule]:=
    Module[{labels,result},
     labels:=    Labels/.{opts}/.Options[BimatrixForm];
     result:= BimatrixF[A,B,labels]   /;(labels=!=Automatic);
     result:= BimatrixF[A,B]          /;(labels==Automatic);
     result];


BimatrixF[a_,b_]:=
Module[ {m,s,r},
         m = Table[Table[TableForm[{StringForm["   ``",b[[i]][[j]]],
                                     StringForm["``",a[[i]][[j]]]}],
             {j,Length[a[[1]]]}],{i,Length[a]}];
         r= Map[Subscripted,Table["R"[i],{i,1,Length[a]}],{1}];
         s= Map[Subscripted,Table["S"[j],{j,1,Length[a[[1]]]}],{1}];
         m = Join[{s},m];
         GridBox[Transpose[Join[{Prepend[r," "]},Transpose[m]]],
                  RowLines -> True, ColumnLines -> True]//FrameBox//DisplayForm
      ];

BimatrixF[a_,b_,{Automatic,labels_}]:=
Module[ {m,s,r},
         m = Table[Table[TableForm[{StringForm["   ``",b[[i]][[j]]],
                                     StringForm["``",a[[i]][[j]]]}],
             {j,Length[a[[1]]]}],{i,Length[a]}];
         r= Map[Subscripted,Table["R"[i],{i,1,Length[a]}],{1}];
         s=labels;
         m = Join[{s},m];
         GridBox[Transpose[Join[{Prepend[r," "]},Transpose[m]]],
                  RowLines -> True, ColumnLines -> True]//FrameBox//DisplayForm
      ];

BimatrixF[a_,b_,{labels_,Automatic}]:=
Module[ {m,s,r},
         m = Table[Table[TableForm[{StringForm["   ``",b[[i]][[j]]],
                                     StringForm["``",a[[i]][[j]]]}],
             {j,Length[a[[1]]]}],{i,Length[a]}];
         s= Map[Subscripted,Table["S"[j],{j,1,Length[a[[1]]]}],{1}];
         r=labels;
         m = Join[{s},m];
         GridBox[Transpose[Join[{Prepend[r," "]},Transpose[m]]],
                  RowLines -> True, ColumnLines -> True]//FrameBox//DisplayForm
      ];

BimatrixF[a_,b_,labels_]:=
Module[ {m,s,r},
         m = Table[Table[TableForm[{StringForm["   ``",b[[i]][[j]]],
                                     StringForm["``",a[[i]][[j]]]}],
             {j,Length[a[[1]]]}],{i,Length[a]}];
         {r,s}=labels;
         m = Join[{s},m];
         GridBox[Transpose[Join[{Prepend[r," "]},Transpose[m]]],
                  RowLines -> True, ColumnLines -> True]//FrameBox//DisplayForm
      ];

Bimatrix[a_,b_]:=
    Table[Table[{a[[i]][[j]],b[[i]][[j]]}, {j,Length[a[[1]]]}], {i,Length[a]}];


maxCliques[edges_List]:=Module[{C,result={},extend},
(* Bron Kerbosch Algorithm *)
     extend[clique_List,cand_List,nolonger_List]:=
              Module[{CLIQUE=clique,CAND=cand,NOLONGER=nolonger,
                      cl,ca,nl,f,U,Xs,X,i,Ls},
                 If[CAND=={},
            (* then output a maximal clique *)
                 AppendTo[result,CLIQUE],
            (* otherwise find a fixpoint *)
                 U=Union[CAND,NOLONGER];
                 Xs=Table[Select[CAND,C[[ #,U[[i]] ]]==0&&#!=U[[i]]&],{i,Length[U]}];
                 Ls=Map[Length,Xs];
                 i=Position[Ls,Min[Ls]][[1,1]];
                 X=Xs[[i]];
                 f=U[[i]];
            (* and make a recursive call to extend *)
                 If[MemberQ[CAND,f],
                     cl=Union[CLIQUE,{f}];
                     ca=Select[CAND,C[[#,f]]==1&];
                     nl=Select[NOLONGER,C[[#,f]]==1&];
                     extend[cl,ca,nl];
                     CAND=Complement[CAND,{f}];
                     NOLONGER=Union[NOLONGER,{f}]];
            (* and backtrack *)
                 For[i=1,i<=Length[X],i++,
                     cl= Union[CLIQUE,{X[[i]]}];
                     ca=Select[CAND,C[[#,X[[i]]]]==1&];
                     nl=Select[NOLONGER,C[[#,X[[i]]]]==1&];
                     extend[cl,ca,nl]] ] ];
(* set the (global) incidence matrix for this connected component *)
     (* C=FromUnorderedPairs[edges][[1]]; !!!!!!!! For Version 4.1 or earlier *)
        C=ToAdjacencyMatrix[FromUnorderedPairs[edges]]; (* Version 4.2 *)
(* start searching *)
      extend[{},Union[Flatten[edges]],{}];
(* return the answer *)
      Union[result] ];    (*  added Union[] 18.10.01  *)

maximalCliques[edges_List]:= Module[{m,e,g,c,x,y,tl,tr,cc},
(* renumber right-hand nodes *)
     m=Max[Table[edges[[i,1]],{i,Length[edges]}]];
     e=Table[{edges[[i,1]],edges[[i,2]]+m},{i,Length[edges]}];
(* convert to a graph *)
     g=FromUnorderedPairs[e];
(* get its connected vertices *)
     c=ConnectedComponents[g];
(* rebuild the edges to get the connected components *)
     cc=Table[ x={};
       For[i=1,i<=Length[e],i++,
          {u,v}=e[[i]];
          For[j=1,j<=Length[c[[k]]],j++,
            If[c[[k]][[j]]==u,AppendTo[x,{u,v}]]]];
       x,
       {k,Length[c]}];
(* connect all left and right hand nodes in each component *)
     cc=Table[
          tl=Union[Table[cc[[i]][[j,1]],{j,Length[cc[[i]]]}]];
          tr=Union[Table[cc[[i]][[j,2]],{j,Length[cc[[i]]]}]];
          tl= Subsets[tl,{2}];
          tr= Subsets[tr,{2}];
          x=Join[cc[[i]],tl,tr];x,{i,Length[cc]}];
(* get maximal cliques with Bron Kerbosch algorithm *)
     cc=Map[maxCliques,cc] ;
(* regroup as bipartite graph and remove extraneous cliques *)
     For[k=1,k<=Length[cc],k++,x=cc[[k]];
        y={};
        For[j=1,j<=Length[x],j++,
           tl=Select[x[[j]],#<=m&];
           tr=Select[x[[j]],#>m&];
           If[tl=!={}&&tr=!={},AppendTo[y,{tl,tr-m}]] ];
        cc[[k]]=y ];
    cc ];

(*
         Interface to lrs
         ----------------
*)
VE[C_,D_,opts___Rule]:= 
               Module[ {verbose,inStream,outStream,A,result,vertices,cobases,b,e,n,m,pos},
               verbose:=    Verbose/.{opts}/.Options[VE]; 
               inStream = OpenTemporary[];
               outStream = OpenTemporary[];
           (* H-representation format for input to lrs *)
               {m,n}=Dimensions[C];
               A=Transpose[Prepend[-Transpose[C],D]]; 
               {m,n}=Dimensions[A];
               Put[OutputForm["game H-representation linearity"],1,m,OutputForm["begin"],m,n,OutputForm["rational"],inStream];
               Table[Table[Put[A[[i,j]],inStream],{j,n}],{i,m}];
               Put[OutputForm["end"],inStream];
               Put[OutputForm["printcobasis"],inStream];
               Close[inStream];
               If[verbose==H,Print["H-Representation"];Print[TableForm[A]]];
           (* Run lrs *)
               Run["lrs",inStream[[1]],outStream[[1]]];
               Close[outStream];
               outStream=OpenRead[outStream[[1]]];
           (* Parse output for vertices and cobases*)
               result=ReadList[outStream,Word,RecordLists->True];
               {{b}}=Position[result,{"begin"}];
               {{e}}=Position[result,{"end"}];
               result=Take[result,{b+2,e-1}];
               vertices=Cases[result,{"1",__}];
               cobases=Table[result[[ Flatten[Position[result,vertices[[i]]]-1]]],{i,Length[vertices]}];
               cobases=Flatten[cobases,1];
               vertices=Map[Drop[#,1]&,ToExpression[vertices,InputForm]];
               {{b}}=Position[cobases[[1]],"facets"];
               {{e}}=Position[cobases[[1]],"det="];
               cobases=Map[Take[#,{b+1,e-2}]&,cobases];
               cobases=ToExpression[cobases,InputForm];
               Close[outStream];
               DeleteFile[{inStream[[1]],outStream[[1]]}]; 
           (* Return result *)
               {vertices,cobases} ];


(*
          Routines for Lemke-Howson
          -------------------------
*)
leaving[T_,s_]:= Module[{E,U,So,t,H},
   lexLess[X_,Y_]:= Module[{i},
           i=Position[Map[#==0&,X-Y],False][[1,1]];
           If[X[[i]]<Y[[i]],True,False]];
   lexMax[S_]:= S[[1]] /;Length[S]==1;        (* singleton *)
   lexMax[S_]:= Module[{Vs,Vmax,posmax,ell},  (* degenerate game *)
               Message[NashEquilibria::degen]; 
               Off[NashEquilibria::degen];
               Vs=Table[T[[S[[i]]]]/T[[S[[i]]]][[s+1]],{i,1,Length[S]}];
               posmax=S[[1]];
               Vmax=Vs[[1]];
               ell=2;
               While[ell<=Length[S],
                  If[lexLess[Vmax,Vs[[ell]]],posmax=S[[ell]];Vmax=Vs[[ell]]];
                  ell++];
               posmax];
   E=-Transpose[T][[1]];
   U=Transpose[T][[s+1]];
   t=Table[If[U[[j]]>0,E[[j]]/U[[j]],1000000],{j,1,Length[T]}];
   So=Flatten[Position[t,Min[t]]];
   lexMax[So]];

(*
          Routines for LCP
          ----------------
*)
CC[M_List,comb_List]:=Module[{C},
                C=IdentityMatrix[Length[M]];
                C[[comb]]=Transpose[M][[comb]];
                Transpose[C]];

ZZ[X_List,comb_List]:= Module[ {Z},
        Z=Table[0,{Length[X]}];
        Z[[comb]]=X[[comb]];
        Z];

FindSol[X_,N_]:=  Module[ {d,k,c,m,b,NT,V},
          {d,k}=Dimensions[N];
          NT=Transpose[N];
          c=Join[Table[0,{i,1,d+1}],Table[1,{i,1,k}]];
          m=ArrayFlatten[{{ NT,-NT.Table[{1},{d}],IdentityMatrix[k] }}];
          b=-X;
          V=LinearProgramming[c,m,b];
          If[ Apply[Plus,Take[V,-k]]==0,
                 X+(Take[V,d]-V[[d+1]]).N,
                 X ] ];




(*
        Option-handling
        ---------------
*)
NashEquilibria[A_List,BB_List:{},opts___Rule]:=
    Module[{select,symbolic,result,B},
     select:=    Select/.{opts}/.Options[NashEquilibria];
     symbolic:=  Symbolic/.{opts}/.Options[NashEquilibria];
     result:= {};
     If[BB=={},B=-A,B=BB];
     result:= NashEq[A]                         /;(symbolic===Automatic)&&(BB==={})&&
                                                  (select===Automatic);
     result:= NashEq[A,B,symbolic]              /;(symbolic=!=Automatic)&&(select==Automatic);
     result:= NashEq[A,B]                       /;(symbolic==Automatic)&&(select==Automatic);
     result:= NashEqAFQS[A,B,symbolic]          /;(symbolic=!=Automatic)&&(select==QS);
     result:= NashEqAFQS[A,B]                   /;(symbolic==Automatic)&&(select==QS);
     result:= NashEqAFESS[A,symbolic]           /;(symbolic=!=Automatic)&&(select==ESS);
     result:= NashEqAFESS[A]                    /;(symbolic==Automatic)&&(select==ESS);
     result:= NashEqAFPerfect[A,B,symbolic]     /;(symbolic=!=Automatic)&&(select==Perfect);
     result:= NashEqAFPerfect[A,B]              /;(symbolic==Automatic)&&(select==Perfect);
     result:= NashEqAF[A,B,symbolic]            /;(symbolic=!=Automatic)&&(select==All);
     result:= NashEqAFv[A,B,symbolic]           /;(symbolic=!=Automatic)&&(select==AllVerbose);
     result:= NashEqAF[A,B]                     /;(symbolic==Automatic)&&(select==All);
     result:= NashEqAFv[A,B]                    /;(symbolic==Automatic)&&(select==AllVerbose);
     result:= NashEqAFMNS[A/.symbolic,B/.symbolic]/;(symbolic=!=Automatic)&&(select==MNS);
     result:= NashEqAFMNS[A,B]                  /;(symbolic==Automatic)&&(select==MNS);
     result:= NashEqLH[A,B,symbolic]            /;(symbolic=!=Automatic)&&(select==One);
     result:= NashEqLH[A,B]                     /;(symbolic==Automatic)&&(select==One);
     result];

(*
        Zero-Sum Games
        --------------
*)
minimax[A_List]:= Module[ {s,b,m,c,u,v},
                s = Min[Flatten[A]];
                b = Table[1,{i,Length[A[[1]]]}];
                c = Table[1,{i,Length[A]}];
                m = Transpose[A-s+1];
                u = LinearProgramming[c,m,b];
                v = 1/Apply[Plus,u];
                {v u,v+s-1} ];

NashEq[A_List]:= Module[{},Message[NashEquilibria::onlyone];
                       {Join[minimax[A],minimax[-Transpose[A]]]}];

(*
        Support Enumeration Algorithm
        -----------------------------
*)
NashEq[AA_List,BB_List]:= Module[
  {M,E,k,m,n,smallest,A,B,R,S,Ts,combs,i,C,X,Z,P,Q,solutions},
   {m,n}=Dimensions[AA];
   k=m+n;
   smallest=Min[Join[AA,BB]];
   A=AA-smallest+1;                 (* ensure positive *)
   B=BB-smallest+1;
   M=ArrayFlatten[{{0,A},{Transpose[B],0}}];
   E=Table[1,{k}];
   R=Range[m];
   S=Range[n]+m;
   Ts=Complement[Subsets[Range[k],{n}],{S}];
   combs=Table[Join[Intersection[R,Ts[[i]]],Complement[S,Ts[[i]]]],{i,Length[Ts]}];
   solutions={};
   Off[LinearSolve::nosol];
   On[NashEquilibria::degen];
   For[ i=1,i<=Length[combs],i++,  (* loop over combinations *)
      C=CC[M,combs[[i]]];
      X=LinearSolve[C,E];
      If[ VectorQ[X]&&Min[X]>=0,          (* a solution *)
              If[Length[NullSpace[C]]==0&&Min[X]==0, (* degeneracy *)
                 Message[NashEquilibria::degen];
                 Off[NashEquilibria::degen]];
              Z=ZZ[X,combs[[i]]];  (* extract the equilibrium *)
              P=Take[Z,m];
              Q=Take[Z,-n];
              P=P/Apply[Plus,P]; Q=Q/Apply[Plus,Q];
              AppendTo[solutions,{P,P.AA.Q,Q,P.BB.Q}] ] ];
   On[LinearSolve::nosol];
   Union[solutions] ];             (* remove duplicates *)
(*
        Mangasarian Avis-Fukuda Algorithm
        ---------------------------------
*)
NashEqAF[A_List,B_List]:= Module[
   {C,D,m,n,Xs,Ys,Ps,Qs,us,vs,em,en,emo,eno,om,on,ilist,jlist,solutions},
   {m,n}=Dimensions[A];
   em=Transpose[{Table[1,{i,1,m}]}];
   en=Transpose[{Table[1,{i,1,n}]}];
   emt=Transpose[em];
   ent =Transpose[en];
   om=Transpose[{Table[0,{i,m}]}];
   on=Transpose[{Table[0,{i,n}]}];
   D = Table[0,{i,1,m+n+1}];
   D[[m+n+1]]=1;
(* Player 1's vertices *)
   C = ArrayFlatten[{{Transpose[B], -en}, {-IdentityMatrix[m], om}, {emt, 0}}];
   Xs=VE[C,D][[1]];
(* Player 2's vertices *)
   C = ArrayFlatten[{{A, -em}, {-IdentityMatrix[n], on}, {ent, 0}}];
   Ys=VE[C,D][[1]];
(* Player 1 *)
   Ps=Transpose[Drop[Transpose[Xs],-1]];
   vs=Transpose[Take[Transpose[Xs],-1]];
(* Player 2 *)
   Qs=Transpose[Drop[Transpose[Ys],-1]];
   us=Transpose[Take[Transpose[Ys],-1]];
   solutions={};
   ilist={};
   jlist={};
   On[NashEquilibria::degen];
   For[ i=1,i<=Length[Ps],i++,
        For[ j=1,j<=Length[Qs],j++,
             If[Ps[[i]].(A+B).Qs[[j]]-vs[[i]]-us[[j]]=={0},
               AppendTo[ilist,i];
               AppendTo[jlist,j];
               AppendTo[solutions,{Ps[[i]],us[[j]][[1]],
                                    Qs[[j]],vs[[i]][[1]]}]] ] ];
(* Check for degeneracy *)
   If[Length[Union[ilist]]!=Length[ilist]||
   Length[Union[jlist]]!=Length[jlist],
       Message[NashEquilibria::degen]];
   Union[solutions]  ];

NashEqAFv[A_List,B_List]:= Module[
   {C,D,m,n,Xs,Ys,Ps,Qs,us,vs,em,en,emo,eno,om,on,ilist,jlist,solutions},
   {m,n}=Dimensions[A];
   em=Transpose[{Table[1,{i,1,m}]}];
   en=Transpose[{Table[1,{i,1,n}]}];
   emt=Transpose[em];
   ent =Transpose[en];
   om=Transpose[{Table[0,{i,m}]}];
   on=Transpose[{Table[0,{i,n}]}];
   D = Table[0,{i,1,m+n+1}];
   D[[m+n+1]]=1;
(* Player 1's vertices *)
   C = ArrayFlatten[{{Transpose[B], -en}, {-IdentityMatrix[m], om}, {emt, 0}}];
   Xs=VE[C,D][[1]];
(* Player 2's vertices *)
   C = ArrayFlatten[{{A, -em}, {-IdentityMatrix[n], on}, {ent, 0}}];
   Print["Player 1"];
   Xs=VE[C,D,Verbose->H][[1]];
   Print["V-Representation"];
   Print[TableForm[Xs]];
(* Player 2's vertices *)
   C = ArrayFlatten[{{A, -em}, {-IdentityMatrix[n], on}, {eno}}];
   Print["Player 2"];
   Ys=VE[C,D,Verbose->H][[1]];
   Print["V-Representation"];
   Print[TableForm[Ys]];
(* Player 1 *)
   Ps=Transpose[Drop[Transpose[Xs],-1]];
   vs=Transpose[Take[Transpose[Xs],-1]];
(* Player 2 *)
   Qs=Transpose[Drop[Transpose[Ys],-1]];
   us=Transpose[Take[Transpose[Ys],-1]];
   solutions={};
   ilist={};
   jlist={};
   On[NashEquilibria::degen];
   For[ i=1,i<=Length[Ps],i++,
        For[ j=1,j<=Length[Qs],j++,
             If[Ps[[i]].(A+B).Qs[[j]]-vs[[i]]-us[[j]]=={0},
               AppendTo[ilist,i];
               AppendTo[jlist,j];
               AppendTo[solutions,{Ps[[i]],us[[j]][[1]],
                                    Qs[[j]],vs[[i]][[1]]}]] ] ];
(* Check for degeneracy *)
   If[Length[Union[ilist]]!=Length[ilist]||
   Length[Union[jlist]]!=Length[jlist],
       Message[NashEquilibria::degen]];
   Union[solutions]  ];

(*
  Maximal Nash Subsets
  --------------------
*)

NashEqAFMNS[A_List,B_List]:= Module[
   {C,D,m,n,Xs,Ys,Ps,Qs,us,vs,em,en,emo,eno,om,on,smallest,plist,qlist,edges,solutions},
   {m,n}=Dimensions[A];
   em=Transpose[{Table[1,{i,1,m}]}];
   en=Transpose[{Table[1,{i,1,n}]}];
   emt=Transpose[em];
   ent =Transpose[en];
   om=Transpose[{Table[0,{i,m}]}];
   on=Transpose[{Table[0,{i,n}]}];
   D = Table[0,{i,1,m+n+1}];
   D[[m+n+1]]=1;
(* Player 1's vertices *)
   C = ArrayFlatten[{{Transpose[B], -en}, {-IdentityMatrix[m], om}, {emt, 0}}];
   Xs=VE[C,D][[1]];
(* Player 2's vertices *)
   C = ArrayFlatten[{{A, -em}, {-IdentityMatrix[n], on}, {ent, 0}}];
   Ys=VE[C,D][[1]];
(* Player 1 *)
   Ps=Transpose[Drop[Transpose[Xs],-1]];
   vs=Transpose[Take[Transpose[Xs],-1]];
(* Player 2 *)
   Qs=Transpose[Drop[Transpose[Ys],-1]];
   us=Transpose[Take[Transpose[Ys],-1]];
   solutions={};
   plist={};
   qlist={};
   On[NashEquilibria::degen];
   For[ i=1,i<=Length[Ps],i++,
        For[ j=1,j<=Length[Qs],j++,
             If[Ps[[i]].(A+B).Qs[[j]]-vs[[i]]-us[[j]]=={0},
               AppendTo[plist,Ps[[i]]];
               AppendTo[qlist,Qs[[j]]];
               AppendTo[solutions,{Ps[[i]],us[[j]][[1]],
                                    Qs[[j]],vs[[i]][[1]]}]] ] ];
(* Check for degeneracy *)
   If[Length[Union[plist]]!=Length[plist]||
   Length[Union[qlist]]!=Length[qlist],
       Message[NashEquilibria::degen]];
   solutions=Union[solutions];
   plist=Union[plist];
   qlist=Union[qlist];
   edges=Table[Flatten[{Position[plist,solutions[[i]][[1]]],
      Position[qlist,solutions[[i]][[3]]]}],{i,Length[solutions]}];
(* return strategies and maximal Nash subsets *)
   {plist,qlist,maximalCliques[edges] }  ];


(*
        Lemke-Howson Algorithm
        ----------------------
*)
NashEqLH[AA_List,BB_List]:=
  Module[{pivot,A,B,smallest,m,n,k,M,C,T,Y,P,Q,beta,r,br,s},
   pivot[i_,j_]:= If[i==r,T[[r,j]]/T[[r,s+1]],
                          T[[i,j]]-T[[r,j]]T[[i,s+1]]/T[[r,s+1]]];
    Message[NashEquilibria::onlyone];
    smallest=Min[Join[AA,BB]];
    A=AA-smallest+1;
    B=BB-smallest+1;
    {m,n}=Dimensions[A];
    k=m+n;
    M=ArrayFlatten[{{0,A},{Transpose[B],0}}];
    C=ArrayFlatten[{{M,IdentityMatrix[k]}}];
    T=ArrayFlatten[{{-Transpose[{Table[1,{i,1,k}]}],C}}];
    beta=Table[i+k,{i,k}];
    s=1;
    br=0;
    While[(br!=1)&&(br!=k+1),
        r=leaving[T,s];
        T=Array[pivot,{k,2*k+1}];
        br= beta[[r]];
        beta[[r]]= s;
        s=If[br>=k+1,br-k,br+k]];
    Y=Table[0,{i,2*k}];
    Table[Y[[beta[[i]]]]=-T[[i,1]],{i,k}];
    P=Take[Y,m];
    P=P/Apply[Plus,P];
    Q=Take[Y,{m+1,k}];
    Q=Q/Apply[Plus,Q];
    {{P,P.AA.Q,Q,P.BB.Q}}   ];

(*
        Symbolic Solutions
        ------------------
*)
NashEq[AAS_List,BBS_List,subs_List]:=
  Module[
     {M,MS,E,k,m,n,smallest,smallestS,A,B,AB,AS,BS,ABS,
      N,R,S,Ts,combs,i,C,CS,X,XS,ZS,r,c,PS,QS,I1S,I2S,solutions},
   A=AAS/.subs; B=BBS/.subs; (* numerical *)
   AS= AAS; BS = BBS;        (* symbolic  *)
   {m,n}=Dimensions[A];
   k=m+n;
   AB = Join[A,B];  (* make positive *)
   ABS = Join[AS,BS];
   smallest=Min[AB];
   {r,c} = Position[AB,smallest,2][[1]];
   smallestS = Part[ABS,r,c];
   A=A-smallest+1;
   B=B-smallest+1;
   AS=AS-smallestS+1;
   BS=BS-smallestS+1;
   M=ArrayFlatten[{{0,A},{Transpose[B],0}}];
   MS=ArrayFlatten[{{0,AS},{Transpose[BS],0}}];
   E=Table[1,{k}];
   R=Range[m];
   S=Range[n]+m;
   Ts=Complement[Subsets[Range[k],{n}],{S}];
   combs=Table[Join[Intersection[R,Ts[[i]]],Complement[S,Ts[[i]]]],{i,Length[Ts]}];
   solutions={};
   Off[LinearSolve::nosol];
   On[NashEquilibria::degen];
   For[i=1,i<=Length[combs],i++,   (* loop on complementary combinations *)
      C=CC[M,combs[[i]]];
      X=LinearSolve[C,E];
      If[ VectorQ[X]&&Min[X]>=0,       (* there exists a solution *)
               If[Min[X]==0,           (* game is degenerate *)
                  Message[NashEquilibria::degen]; Off[NashEquilibria::degen]];
               CS = CC[MS,combs[[i]]]; (* get the symbolic equivalent *)
               XS = LinearSolve[CS,E];
               If[ VectorQ[XS]&&Min[XS/.subs]>=0,
                   ZS = ZZ[XS,combs[[i]]];
                   PS = Take[ZS,m];
                   QS = Take[ZS,-n];
                   PS=Simplify[PS/Apply[Plus,PS]];
                   QS=Simplify[QS/Apply[Plus,QS]];
                   I1S = Simplify[PS.AAS.QS];
                   I2S = Simplify[PS.BBS.QS];
                   AppendTo[solutions,{PS,I1S,QS,I2S}] ] ] ];
    On[LinearSolve::nosol];
    Union[solutions] ];    (* remove duplicates *)


NashEqAF[AS_List,BS_List,subs_List]:= Module[
   {A,B,CS1,CS2,C,D,m,n,em,en,eno,emo,om,on,ve,sol,i,j,
   bvs1,bvs2,beta,X,Y,Xs,Ys,Ps,Qs,us,vs,P,Q,u,v,ilist,jlist,solutions},
   A=AS/.subs;
   B=BS/.subs;
   {m,n}=Dimensions[A];
   em=Transpose[{Table[1,{i,1,m}]}];
   en=Transpose[{Table[1,{i,1,n}]}];
   emt=Transpose[em];
   ent =Transpose[en];
   om=Transpose[{Table[0,{i,m}]}];
   on=Transpose[{Table[0,{i,n}]}];
   D = Table[0,{i,1,m+n+1}];
   D[[m+n+1]]=1;
(* Symbolic matrices *)
   CS1 = ArrayFlatten[{{Transpose[BS], -en}, {-IdentityMatrix[m], om}, {emt,0}}];
   CS2 = ArrayFlatten[{{AS,            -em}, {-IdentityMatrix[n], on}, {ent,0}}];
(* Player 1's vertices and bases *)
   C = ArrayFlatten[{{Transpose[B], -en}, {-IdentityMatrix[m], om}, {emt,0}}];
   ve=VE[C,D];
   Xs=ve[[1]];
   bvs1=ve[[2]];
(* Player 2's vertices and bases *)
   C = ArrayFlatten[{{A, -em}, {-IdentityMatrix[n], on}, {ent,0}}];
   ve=VE[C,D];
   Ys=ve[[1]];
   bvs2=ve[[2]];
(* Player 1's strategies and payoffs *)
   Ps=Transpose[Drop[Transpose[Xs],-1]];
   vs=Transpose[Take[Transpose[Xs],-1]];
(* Player 2's strategies and payoffs *)
   Qs=Transpose[Drop[Transpose[Ys],-1]];
   us=Transpose[Take[Transpose[Ys],-1]];
   solutions={};
   ilist={};
   jlist={};
   On[NashEquilibria::degen];
(* Loop on vertex combinations for symbolic equilibria *)
   For[ i=1,i<=Length[Ps],i++,
        For[ j=1,j<=Length[Qs],j++,
             If[Ps[[i]].(A+B).Qs[[j]]-vs[[i]]-us[[j]]=={0},
               AppendTo[ilist,i];
               AppendTo[jlist,j];
(* returned basis sets don't include the linearity!! *)
               beta=Append[bvs1[[i]],m+n+1]; 
               X = LinearSolve[ CS1[[beta]],D[[beta]] ];
               P=Simplify[Take[X,m]];
               v=Simplify[X[[m+1]]];
               beta=Append[bvs2[[j]],m+n+1];
               Y = LinearSolve[ CS2[[beta]],D[[beta]] ];
               Q=Simplify[Take[Y,n]];
               u=Simplify[Y[[n+1]]];
               AppendTo[solutions,{P,u,Q,v}]]]];
(* Check for degeneracy *)
   If[Length[Union[ilist]]!=Length[ilist]||
   Length[Union[jlist]]!=Length[jlist],
       Message[NashEquilibria::degen]];
   Union[solutions]  ];

NashEqAFv[AS_List,BS_List,subs_List]:= Module[
   {A,B,CS1,CS2,C,D,m,n,em,en,eno,emo,om,on,ve,sol,i,j,
   bvs1,bvs2,beta,X,Y,Xs,Ys,Ps,Qs,us,vs,P,Q,u,v,ilist,jlist,solutions},
   A=AS/.subs;
   B=BS/.subs;
   {m,n}=Dimensions[A];
   em=Transpose[{Table[1,{i,1,m}]}];
   en=Transpose[{Table[1,{i,1,n}]}];
   emt=Transpose[em];
   ent=Transpose[en];
   om=Transpose[{Table[0,{i,m}]}];
   on=Transpose[{Table[0,{i,n}]}];
   D = Table[0,{i,1,m+n+1}];
   D[[m+n+1]]=1;
(* Symbolic matrices *)
   CS1 = ArrayFlatten[{{Transpose[BS], -en}, {-IdentityMatrix[m], om}, {emt,0}}];
   CS2 = ArrayFlatten[{{AS,            -em}, {-IdentityMatrix[n], on}, {ent,0}}];
(* Player 1's vertices and bases *)
   C = ArrayFlatten[{{Transpose[B], -en}, {-IdentityMatrix[m], om}, {emt,0}}];
   Print["Player 1"];
   ve=VE[C,D,Verbose->H];
   Xs=ve[[1]];
   bvs1=ve[[2]];
   Print["V-Representation"];
   Print[TableForm[Xs]];
   Print["Basis index sets (excluding normalization)"];
   Print[TableForm[bvs1]];   
(* Player 2's vertices and bases *)
   C = ArrayFlatten[{{A, -em}, {-IdentityMatrix[n], on}, {ent,0}}];
   Print["Player 1"];
   ve=VE[C,D,Verbose->H];
   Ys=ve[[1]];
   bvs2=ve[[2]];
   Print["V-Representation"];
   Print[TableForm[Ys]];
   Print["Basis index sets (excluding normalization)"];
   Print[TableForm[bvs2]];  
(* Player 1's strategies and payoffs *)
   Ps=Transpose[Drop[Transpose[Xs],-1]];
   vs=Transpose[Take[Transpose[Xs],-1]];
(* Player 2's strategies and payoffs *)
   Qs=Transpose[Drop[Transpose[Ys],-1]];
   us=Transpose[Take[Transpose[Ys],-1]];
   solutions={};
   ilist={};
   jlist={};
   On[NashEquilibria::degen];
(* Loop on vertex combinations for symbolic equilibria *)
   For[ i=1,i<=Length[Ps],i++,
        For[ j=1,j<=Length[Qs],j++,
             If[Ps[[i]].(A+B).Qs[[j]]-vs[[i]]-us[[j]]=={0},
               AppendTo[ilist,i];
               AppendTo[jlist,j];
(* returned basis sets don't include the linearity!! *)
               beta=Append[bvs1[[i]],m+n+1]; 
               X = LinearSolve[ CS1[[beta]],D[[beta]] ];
               P=Simplify[Take[X,m]];
               v=Simplify[X[[m+1]]];
               beta=Append[bvs2[[j]],m+n+1];
               Y = LinearSolve[ CS2[[beta]],D[[beta]] ];
               Q=Simplify[Take[Y,n]];
               u=Simplify[Y[[n+1]]];
               AppendTo[solutions,{P,u,Q,v}]]]];
(* Check for degeneracy *)
   If[Length[Union[ilist]]!=Length[ilist]||
   Length[Union[jlist]]!=Length[jlist],
       Message[NashEquilibria::degen]];
   Union[solutions]  ];


NashEqLH[AAS_List,BBS_List,subs_List]:=
  Module[{pivot,A,B,AB,AS,BS,ABS,DS,smallest,smallestS,rr,cc,
          m,n,k,M,MS,C,CS,T,ES,YS,P,Q,I1,I2,beta,r,s},
   pivot[i_,j_]:= If[i==r,T[[r,j]]/T[[r,s+1]],T[[i,j]]-T[[r,j]]*T[[i,s+1]]/T[[r,s+1]]];
    Message[NashEquilibria::onlyone];
    A=AAS/.subs;
    B=BBS/.subs;
    AB=Join[A,B];
    ABS = Join[AAS,BBS];
    smallest=Min[AB];
    {rr,cc} = Position[AB,smallest,2][[1]];
    smallestS = Part[ABS,rr,cc];
    A=A-smallest+1;
    B=B-smallest+1;
    AS=AAS-smallestS+1;
    BS=BBS-smallestS+1;
    {m,n}=Dimensions[A];
    k=m+n;
    M=ArrayFlatten[{{0,A},{Transpose[B],0}}];
    MS=ArrayFlatten[{{0,AS},{Transpose[BS],0}}];
    C=ArrayFlatten[{{M,IdentityMatrix[k]}}];
    CS=ArrayFlatten[{{MS,IdentityMatrix[k]}}];
    T=ArrayFlatten[{{-Transpose[{Table[1,{i,1,k}]}],C}}];
    beta=Table[i+k,{i,k}];
    s=1;
    br=0;
    While[(br!=1)&&(br!=k+1),
        r=leaving[T,s];
        T=Array[pivot,{k,2*k+1}];
        br= beta[[r]];
        beta[[r]]= s;
        s=If[br>=k+1,br-k,br+k]];
    YS=Table[0,{i,2*k}];
    DS= Transpose[Transpose[CS][[beta]]];
    ES= LinearSolve[DS,Table[1,{i,k}]];
    Table[YS[[beta[[i]]]]=ES[[i]],{i,k}];
    P=Take[YS,m];
    P=P/Apply[Plus,P]//Simplify;
    Q=Take[YS,{m+1,k}];
    Q=Q/Apply[Plus,Q]//Simplify;
    I1=P.AAS.Q//Simplify;
    I2=P.BBS.Q//Simplify;
    {{P,I1,Q,I2}}  ];

(*
        Equilibrium Selection
        ---------------------

   Perfect  *)

NashEqAFPerfect[A_List,B_List]:= Module[ {NE,crit},
(* criterion for perfectness *)
crit[{P_List,_,Q_List,_}]:= Undominated[P,A]&&Undominated[Q,Transpose[B]];
(* first get the  Nash equilibria *)
    NE =  NashEqAF[A,B];
(* Apply criterion *)
    Select[NE,crit] ];

NashEqAFPerfect[A_List,B_List,subs_List]:= Module[ {NE,r,AA,BB,crit},
(* criterion for perfectness *)
crit[{P_List,_,Q_List,_}]:= Undominated[P,AA]&&Undominated[Q,Transpose[BB]];
(* first create the numerical matrices used in crit *)
   AA = A/.subs; BB = B/.subs;
(* Get the  Nash equilibria in symbolic form *)
    NE = NashEqAF[A,B,subs];
(* now get the positions on the list which are perfect equilibria *)
    r = Flatten[Position[Map[crit,NE/.subs],True]];
(* and select them from the symbolic list *)
    NE[[r]]  ];

(*
   Quasistrict
*)

NashEqAFQS[A_List,B_List]:= Module[ {NE,crit,Cx,Bx,Cy,By},
(* Criterion for quasi-strict equilibria *)
crit[{x_List,_,y_List,_}]:=(
   (* carrier of x *)
   Cx=Flatten[Position[Map[NonPositive,x],False]];
   (* extended carrier of x *)
   Bx=Flatten[Position[Map[NonNegative,A.y-x.A.y],True]];
   (* carrier of y *)
   Cy=Flatten[Position[Map[NonPositive,y],False]];
   (* extended carrier of y *)
   By=Flatten[Position[Map[NonNegative,x.B-x.B.y],True]];
   (* if quasi-strict, return True *)
   (Cx==Bx)&&(Cy==By) );
(* first get the  Nash equilibria *)
    NE =  NashEqAF[A,B];
(* Apply criterion *)
    Select[NE,crit] ];

NashEqAFQS[A_List,B_List,subs_List]:= Module[ {NE,r,crit,AA,BB,Cx,Bx,Cy,By},
(* Criterion for quasi-strict equilibria *)
crit[{x_List,_,y_List,_}]:=(
   (* carrier of x *)
   Cx=Flatten[Position[Map[NonPositive,x],False]];
   (* extended carrier of x *)
   Bx=Flatten[Position[Map[NonNegative,AA.y-x.AA.y],True]];
   (* carrier of y *)
   Cy=Flatten[Position[Map[NonPositive,y],False]];
   (* extended carrier of y *)
   By=Flatten[Position[Map[NonNegative,x.BB-x.BB.y],True]];
   (* if quasi-strict, return True *)
   (Cx==Bx)&&(Cy==By) );
(* first create the numerical matrices used in crit *)
   AA = A/.subs; BB = B/.subs;
(* then get the  Nash equilibria in symbolic form *)
    NE =  NashEqAF[A,B,subs];
(* now get the positions on the list which are quasi-strict *)
    r = Flatten[Position[Map[crit,NE/.subs],True]];
(* and select them from the symbolic list *)
    NE[[r]]  ];

(*
     ESS
*)

NashEqAFESS[A_List]:= Module[ {SNE,crit,s,k,B,C},
(* Haigh's criterion for ESS *)
crit[{x_List,_,_,_}]:=(
   (* extended carrier of x *)
   s=Flatten[Position[Map[NonNegative,A.x-x.A.x],True]];
   k=Length[s];
   (* if the carrier is a singleton, return True *)
   If[k==1,Return[True]];
   B=Transpose[Transpose[A[[s]]][[s]]];
   C=Table[B[[i,j]]+B[[k,k]]-B[[i,k]]-B[[k,j]],{i,k-1},{j,k-1}];
   Return[Max[Chop[N[Eigenvalues[C+Transpose[C]]]]]<0] );
(* first get the symmetric Nash equilibria *)
    SNE = Cases[ NashEqAF[A,Transpose[A]],{a_,b_,a_,b_} ];
(* Apply Haigh's criterion *)
    Select[SNE,crit] ];

NashEqAFESS[A_List,subs_List]:= Module[ {crit,s,r,k,AA,B,C,SNE},
(* Haigh's criterion for ESS *)
crit[{x_List,_,_,_}]:=(
(* extended carrier of x *)
   s=Flatten[Position[Map[NonNegative,AA.x-x.AA.x],True]];
   k=Length[s];
(* if the carrier is a singleton, return True *)
   If[k==1,Return[True]];
   B=Transpose[Transpose[AA[[s]]][[s]]];
   C=Table[B[[i,j]]+B[[k,k]]-B[[i,k]]-B[[k,j]],{i,k-1},{j,k-1}];
   Return[Max[Chop[N[Eigenvalues[C+Transpose[C]]]]]<0] );
(* first create the numerical matrix used in crit *)
   AA = A/.subs;
(* then get the list of symmetric Nash equilibria in symbolic form *)
    SNE = Cases[NashEqAF[A,Transpose[A],subs],{a_,b_,a_,b_}];
(* now get the positions on the list which satisfy Haigh's criterion *)
    r = Flatten[Position[Map[crit,SNE/.subs],True]];
(* and select them from the symbolic list *)
    SNE[[r]]  ];


(*
        Domination
        ----------
*)
Undominated[P_List,A_List]:= Module[
             {Ap,s,c,m,b,n1,m1,n0,nn0,mm0,v},
                Ap = Transpose[Transpose[A]-P.A];
                If[minimax[Ap][[2]]==0,
                   s = Min[Flatten[Ap]];
                   Ap = Ap - s + 1;
                   m1 = Table[1,{i,Length[A]}];
                   n1 = Table[1,{j,Length[A[[1]]]}];
                   n0 = Table[0,{j,Length[A[[1]]]}];
                   c = Join[-Ap.n1,n0];
                   b = Join[{0,0},n1,-m1];
                   m = ArrayFlatten[{{ {m1},-{n1}},
                                    {-{m1}, {n1}},
                                    {Transpose[Ap],0},
                                    {0,-Ap}}];
                   v = LinearProgramming[c,m,b];
                   If[-v.c==Length[A[[1]]],True,False],
                          False] ];




