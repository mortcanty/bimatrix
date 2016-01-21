NashEquilibria::degen = "degenerate game";
NashEquilibria::onlyone = "only one solution will be generated";

Options[NashEquilibria] = {Select -> Automatic, Symbolic -> Automatic}
Options[BimatrixForm] = {Labels -> Automatic}


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

(*
        Lemke-Howson Algorithm
        ----------------------
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
    On[NashEquilibria::degen];
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
    On[NashEquilibria::degen];
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
        Support Enumeration Algorithm
        -----------------------------
*)

CC[M_List,comb_List]:=Module[{C},
                C=IdentityMatrix[Length[M]];
                C[[comb]]=Transpose[M][[comb]];
                Transpose[C]];

ZZ[X_List,comb_List]:= Module[ {Z},
        Z=Table[0,{Length[X]}];
        Z[[comb]]=X[[comb]];
        Z];

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

