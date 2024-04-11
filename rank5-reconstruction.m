// This code verifies the algebraic claims made in the proof of Proposition 3.1, Case 2, from the paper "Conic bundle threefolds differing by a constant Brauer class and connections to rationality" by Sarah Frei, Lena Ji, Soumya Sankar, Bianca Viray, and Isabel Vogt.

AA<a,b,g2,h2,i2,j2,k2,f3,g3,h3,i3,j3,k3> := PolynomialRing(Rationals(), 2+5 + 6);
K<a,b,g2,h2,i2,j2,k2,f3,g3,h3,i3,j3,k3> := FieldOfFractions(AA);

R<u,v,w> := PolynomialRing(K, 3);
F<u,v,w> := FieldOfFractions(R);

S<T> := PolynomialRing(K);

M1 := Matrix([[0,0,0], [0,a,0],[0,0,b]]);
M2 := Matrix([[-Determinant(Submatrix(M1,[2,3],[2,3])),g2,h2], [g2,i2,j2],[h2,j2,k2]]);
M3 := Matrix([[f3,g3,h3], [g3,i3,j3],[h3,j3,k3]]);

N1 := Submatrix(M1, [2,3],[2,3]);
assert M1 eq DiagonalJoin(ZeroMatrix(Parent(N1[1][1]), 1, 1), N1);

Q1 := (Matrix(R,[[u,v,w]])*ChangeRing(M1,R)*Matrix(R,[[u],[v],[w]]))[1][1];
Q2 := (Matrix(R,[[u,v,w]])*ChangeRing(M2,R)*Matrix(R,[[u],[v],[w]]))[1][1];
Q3 := (Matrix(R,[[u,v,w]])*ChangeRing(M3,R)*Matrix(R,[[u],[v],[w]]))[1][1];



qinfTopLeft :=  ZeroMatrix(K,3,3);
qinfBottomRight := DiagonalJoin(Matrix([[K!2]]), ZeroMatrix(K,2,2));
qinfTopRight := DiagonalJoin(ZeroMatrix(K, 1,1), IdentityMatrix(K,2));
qinfBottomLeft := Transpose(qinfTopRight);
Ainf := VerticalJoin(
    HorizontalJoin(   qinfTopLeft,     qinfTopRight), 
    HorizontalJoin(qinfBottomLeft, qinfBottomRight));

D1 := qinfBottomRight;
D2 := qinfTopRight;

T2 := M2;
T2[2][1] := 0;
T2[3][1] := 0;
T2[3][2] := 0;
T2[1][2] := 2*T2[1][2];
T2[1][3] := 2*T2[1][3];
T2[2][3] := 2*T2[2][3];
assert T2 + Transpose(T2) eq 2*M2;
assert IsUpperTriangular(T2);

q0TopLeft := DiagonalJoin(IdentityMatrix(K,1), -a*b*N1^(-1));
q0BottomLeft := -ChangeRing(T2,K)*ChangeRing(DiagonalJoin(ZeroMatrix(K,1,1), N1^(-1)), K);
q0TopRight := Transpose(q0BottomLeft);

q0BottomRight := 1/(a*b)*(M3 + T2*(DiagonalJoin(ZeroMatrix(K,1,1),-N1^(-1)))*Transpose(T2));

A0 := VerticalJoin(
    HorizontalJoin(   q0TopLeft,     q0TopRight), 
    HorizontalJoin(q0BottomLeft, q0BottomRight));


/*******************************/
//check Schur complement formula
assert Determinant(A0 - T*Ainf) eq Determinant(q0TopLeft)*Determinant(
    (q0BottomRight - q0BottomLeft*q0TopLeft^(-1)*q0TopRight)
    + T*(D2*q0TopLeft^(-1)*q0TopRight + q0BottomLeft*q0TopLeft^(-1)*D2 - D1)
    + T^2*(-D2*q0TopLeft^(-1)*D2)
);

//checking genus 2 curves agree
assert Determinant(q0TopLeft)*(q0BottomRight - q0BottomLeft*q0TopLeft^(-1)*q0TopRight) eq M3;
assert Determinant(q0TopLeft)*(D2*q0TopLeft^(-1)*q0TopRight + q0BottomLeft*q0TopLeft^(-1)*D2 - D1) eq 2*M2;
assert Determinant(q0TopLeft)*(-D2*q0TopLeft^(-1)*D2) eq M1;

assert Determinant(q0TopLeft)^2*Determinant(A0 - T*Ainf) eq Determinant(M3 + 2*T*M2 + T^2*M1);
/*******************************/

Bp := Matrix(R, [
    [1, 0,   0,   0],
    [ 0,-w, -u^2,  0],
    [ 0, v, 0,   -u^2],
    [ 0, 0, u*v, u*w],
    [ 0, 0, v*v, v*w],
    [ 0, 0, w*v, w*w]]);

assert ZeroMatrix(R, 4, 4) eq Transpose(Bp)*ChangeRing(Ainf, R)*Bp;

temp := Transpose(Bp)*ChangeRing(A0, R)*Bp;

assert Rank(temp) eq 3;
assert temp eq DiagonalJoin(Submatrix(temp,[1],[1]), Submatrix(temp,[2,3,4],[2,3,4]));
assert temp[1][1] eq 1;

//Brauer class given by Brauer class associated to rank 2 quadratic form -Submatrix(temp,[2,3,4],[2,3,4]);

bM := -Submatrix(temp, [2,3],[2,3]);
// Brauer class is given by bM[1][1] and -Determinant(bM)

assert bM[1][1] eq Q1;
assert -Determinant(bM) eq -1/(a*b)*v^2*(Q2^2 - Q1*Q3); 

//Bl_C Z has generic fiber equal to
// (Q1, -ab*(Q2^2 - Q1Q3)) in the Brauer group

/*******************************/


