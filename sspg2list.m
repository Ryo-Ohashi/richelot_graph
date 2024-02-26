load "tables.m";

p := 97;
K := GF(p^2);
R<x> := PolynomialRing(K);
i := Roots(x^2+1)[1][1];

load "functions.m";

function number_of_sspg2curve()
    assert p gt 5;
    num := (p^3 + 24*p^2 + 141*p - 166)/2880;
    num -:= (1-LegendreSymbol(-1,p))/32;
    num +:= (1-LegendreSymbol(-2,p))/8;
    num +:= (1-LegendreSymbol(-3,p))/18;
    if p mod 5 eq 4 then
        num := num + 4/5;
    end if;
    return Integers()!num;
end function;

limit := number_of_sspg2curve();
time sspg2list := listup_sspg2curve(limit);
