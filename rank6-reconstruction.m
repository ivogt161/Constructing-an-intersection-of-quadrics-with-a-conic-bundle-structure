// This code verifies the algebraic claims made in the proof of Proposition 3.1, Case 1, from the paper "Conic bundle threefolds differing by a constant Brauer class and connections to rationality" by Sarah Frei, Lena Ji, Soumya Sankar, Bianca Viray, and Isabel Vogt.

AA<a,b,f2,g2,h2,i2,j2,k2,f3,g3,h3,i3,j3,k3> := PolynomialRing(Rationals(), 3*6);
K<a,b,f2,g2,h2,i2,j2,k2,f3,g3,h3,i3,j3,k3> := FieldOfFractions(AA);

R<u,v,w> := PolynomialRing(K, 3);
F<u,v,w> := FieldOfFractions(R);

M1 := Matrix([[a,0,0], [0,b,0],[0,0,-a*b]]);
M2 := Matrix([[f2,g2,h2], [g2,i2,j2],[h2,j2,k2]]);
M3 := Matrix([[f3,g3,h3], [g3,i3,j3],[h3,j3,k3]]);

Q1 := (Matrix(R,[[u,v,w]])*ChangeRing(M1,R)*Matrix(R,[[u],[v],[w]]))[1][1];
Q2 := (Matrix(R,[[u,v,w]])*ChangeRing(M2,R)*Matrix(R,[[u],[v],[w]]))[1][1];
Q3 := (Matrix(R,[[u,v,w]])*ChangeRing(M3,R)*Matrix(R,[[u],[v],[w]]))[1][1];

Delta := Q2^2 - Q1*Q3;

assert (a*b)^2 eq -Determinant(M1);

//Our reconstruction formulas
q0TopLeft := a*b*M1^(-1);
q0BottomLeft := -(M2)*ChangeRing(M1,K)^(-1);
q0TopRight:= Transpose(q0BottomLeft);
assert q0TopRight eq -ChangeRing(M1,K)^(-1)*M2;
q0BottomRight := (-1/(a*b))*(M3 - (M2)*ChangeRing(M1, K)^(-1)*M2);

Id3 := IdentityMatrix(K,3);
Zero3 := ZeroMatrix(K,3,3);

// //Our forward formulas
// assert -Adjoint(A) eq M1;
// assert (1/2)*(B*Adjoint(A) + Adjoint(A)*Transpose(B)) eq M2;
// assert Determinant(A)*Atilde - B*Adjoint(A)*Transpose(B) eq M3;

A0 := VerticalJoin(
    HorizontalJoin(ChangeRing(q0TopLeft, K), q0TopRight), 
    HorizontalJoin(           q0BottomLeft,  q0BottomRight));

Ainf := VerticalJoin(
    HorizontalJoin(Zero3, Id3), 
    HorizontalJoin(  Id3, Zero3));

RestrictToPlane := Matrix(R, [
    [-v,-w, 0, 0],
    [ u, 0,-w, 0],
    [ 0, u, v, 0],
    [ 0, 0, 0, u],
    [ 0, 0, 0, v],
    [ 0, 0, 0, w]]);

//\textbf{M} is the symmetric matrix corresponding to Bl_C Z over the affine plane where w != 0
bM := Submatrix(Transpose(RestrictToPlane)*ChangeRing(A0, R)*RestrictToPlane, [2,3,4],[2,3,4]);
DiagMatrixbM := Diagonalization(bM);
assert Minor(bM, [1], [1]) eq -u^2 + b*w^2;
assert Minor(bM, [1,2], [1,2]) eq -Q1*w^2;
assert Minor(bM, [1,2,3], [1,2,3]) eq (-w^2/(a*b))*(Q2^2 - Q1*Q3);

DiagEntriesbM := [DiagMatrixbM[i][i] : i in [1,2,3]];
assert DiagEntriesbM eq 
    [
        Minor(bM, [1], [1]), 
        Minor(bM, [1,2], [1,2])/Minor(bM, [1], [1]), 
        Minor(bM, [1,2,3], [1,2,3])/Minor(bM, [1,2], [1,2])
    ];
d1,d2,d3 := Explode(DiagEntriesbM);

// conic is d1*X^2 + d2*Y^2 + d3*Z^3, which we can rearrange to
//         -d1*d3*X^2 - d2*d3Y^2 = (d3*Z)^2
//  so is given by Brauer class 
//  (-d1*d3, -d2*d3) = (-d1*d3, d1*d3) + (-d1*d3, -d2*d3)
//                   = (-d1*d3, -d1*d2) 
//                   = (-d1*d3, -d1*d2)  + (d1*d2, - d1*d2)
//                   = (-d1^2*d2*d3,           -d1*d2)
//                   = (-d1^2*d2*d3*(a*b/w)^2, -d1*d2*w^(-2))

assert -d1^2*d2*d3*(a*b/w)^2 eq -a*b*(u^2 - b*w^2)*(Q2^2 - Q1*Q3);
assert -d1*d2*w^(-2) eq Q1;


