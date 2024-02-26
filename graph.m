load "tables.m";

p := 97;
K := GF(p^2);
R<x> := PolynomialRing(K);
i := Roots(x^2+1)[1][1];

load "functions.m";

time node_set, edge_set := compute_sspg2graph();
