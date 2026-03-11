%--------------------------------------------------------------------------
% File     : MGT001+1 : TPTP v9.2.0. Released v2.0.0.
% Domain   : Management (Organisation Theory)
% Problem  : Selection favors organizations with high inertia
% Version  : [PB+94] axioms.
% English  : Selection within populations of organizations in modern
%            societies favours organizations whose structure have high
%            inertia.

% Refs     : [PB+92] Peli et al. (1992), A Logical Approach to Formalizing
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
% Source   : [Kam94]
% Names    : THEOREM 1 [PB+92]
%          : T1FOL3 [PB+94]

% Status   : Theorem
% Rating   : 0.10 v9.1.0, 0.00 v7.5.0, 0.05 v7.4.0, 0.00 v7.0.0, 0.07 v6.4.0, 0.00 v6.1.0, 0.12 v6.0.0, 0.50 v5.5.0, 0.12 v5.4.0, 0.17 v5.3.0, 0.26 v5.2.0, 0.00 v5.0.0, 0.05 v4.1.0, 0.06 v4.0.1, 0.05 v3.7.0, 0.00 v3.2.0, 0.11 v3.1.0, 0.00 v2.1.0
% Syntax   : Number of formulae    :    7 (   0 unt;   0 def)
%            Number of atoms       :   48 (   0 equ)
%            Maximal formula atoms :   11 (   6 avg)
%            Number of connectives :   41 (   0   ~;   0   |;  32   &)
%                                         (   2 <=>;   7  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   21 (  13 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    8 (   8 usr;   0 prp; 2-3 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :   45 (  42   !;   3   ?)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
fof(mp1,axiom,
    ! [X,T] :
      ( organization(X,T)
     => ? [R] : reliability(X,R,T) ) ).

fof(mp2,axiom,
    ! [X,T] :
      ( organization(X,T)
     => ? [A] : accountability(X,A,T) ) ).

fof(mp3,axiom,
    ! [X,T] :
      ( organization(X,T)
     => ? [Rp] : reproducibility(X,Rp,T) ) ).

%----Selection in populations of organizations in modern societies favours
%----forms with high reliability of performance and high levels of
%----accountability.
fof(a1_FOL,hypothesis,
    ! [X,Y,R1,R2,A1,A2,P1,P2,T1,T2] :
      ( ( organization(X,T1)
        & organization(Y,T2)
        & reliability(X,R1,T1)
        & reliability(Y,R2,T2)
        & accountability(X,A1,T1)
        & accountability(Y,A2,T2)
        & survival_chance(X,P1,T1)
        & survival_chance(Y,P2,T2)
        & greater(R2,R1)
        & greater(A2,A1) )
     => greater(P2,P1) ) ).

%----Reliability and accountability require that organizational structures
%----be highly reproducible.
fof(a2_FOL,hypothesis,
    ! [X,Y,T1,T2,R1,R2,A1,A2,Rp1,Rp2] :
      ( ( organization(X,T1)
        & organization(Y,T2)
        & reliability(X,R1,T1)
        & reliability(Y,R2,T2)
        & accountability(X,A1,T1)
        & accountability(Y,A2,T2)
        & reproducibility(X,Rp1,T1)
        & reproducibility(Y,Rp2,T2) )
     => ( greater(Rp2,Rp1)
      <=> ( greater(R2,R1)
          & greater(A2,A1) ) ) ) ).

%----High levels of reproducibility of structure generate strong
%----inertial pressures.
fof(a3_FOL,hypothesis,
    ! [X,Y,T1,T2,Rp1,Rp2,I1,I2] :
      ( ( organization(X,T1)
        & organization(Y,T2)
        & reorganization_free(X,T1,T1)
        & reorganization_free(Y,T2,T2)
        & reproducibility(X,Rp1,T1)
        & reproducibility(Y,Rp2,T2)
        & inertia(X,I1,T1)
        & inertia(Y,I2,T2) )
     => ( greater(Rp2,Rp1)
      <=> greater(I2,I1) ) ) ).

fof(t1_FOL,conjecture,
    ! [X,Y,T1,T2,I1,I2,P1,P2] :
      ( ( organization(X,T1)
        & organization(Y,T2)
        & reorganization_free(X,T1,T1)
        & reorganization_free(Y,T2,T2)
        & inertia(X,I1,T1)
        & inertia(Y,I2,T2)
        & survival_chance(X,P1,T1)
        & survival_chance(Y,P2,T2)
        & greater(I2,I1) )
     => greater(P2,P1) ) ).

%--------------------------------------------------------------------------
