% Simple group theory — commutativity is NOT a theorem
% mace4 should find a countermodel

fof(right_identity, axiom, ![X]: (f(X,e) = X)).
fof(right_inverse, axiom, ![X]: (f(X,g(X)) = e)).
fof(associativity, axiom, ![X,Y,Z]: (f(f(X,Y),Z) = f(X,f(Y,Z)))).
fof(commutativity, conjecture, ![X,Y]: (f(X,Y) = f(Y,X))).
