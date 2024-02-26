// Return a theta null-point corresponding to the square of a supersingular elliptic curve.
function generate_sspsurfnull()
    j := jInvariant(SupersingularEllipticCurve(K)); t := Roots(256*(x^2-x+1)^3-j*(x^2-x)^2,K)[1][1];
    prod_null := [K!0: j in [1..16]];
    prod_null[1] := 1;
    prod_null[2] := Sqrt(t);                    prod_null[3] := prod_null[2];
    prod_null[4] := t;
    prod_null[5] := Sqrt(1-t);                  prod_null[9] := prod_null[5];
    prod_null[7] := prod_null[2]*prod_null[5];  prod_null[10]:= prod_null[7];
    prod_null[13]:= 1-t;
    return j, prod_null;
end function;

// For a given theta null-point and lists corresonding to a symplectic matrix, return the transformed theta null-point by the matrix.
function transform_nullpoint(null,index_list,sign_list)
    trans_null := [K!0: j in [1..16]];
    for num in [0,1,2,3,4,6,8,9,12,15] do
        index := index_list[num+1]; sign := sign_list[num+1];
        if sign eq 0 then
            trans_null[index+1] :=    null[num+1];
        elif sign eq 1 then
            trans_null[index+1] :=  i*null[num+1];
        elif sign eq 2 then
            trans_null[index+1] :=   -null[num+1];
        else
            trans_null[index+1] := -i*null[num+1];
        end if;
    end for;
    return trans_null;
end function;

// For a given theta null-point on Omega/2, return the theta null-point on Omega.
function compute_twoisogeny(full_null)
    sqrt_null := [K!0: j in [1..4]]; image_null := [K!0: j in [1..16]];
    if full_null[1] ne 0 then
        sqrt_null[1] := full_null[1]; for k in [2..4] do sqrt_null[k] := Sqrt(full_null[1]*full_null[k]); end for;
    else
        sqrt_null[2] := full_null[2]; for k in [3..4] do sqrt_null[k] := Sqrt(full_null[2]*full_null[k]); end for;
    end if;
    product_matrix := Matrix(4,4,[<j,k,sqrt_null[j]*sqrt_null[k]>: j in [1..k], k in [1..4]]); 
    for num in [0,1,2,3,4,6,8,9,12,15] do
        value := 0;
        for k in [1..4] do
            index := isogy_table[1][k][num+1]+1; min := Min(index,k); max := Max(index,k);
            if isogy_table[2][k][num+1] eq 0 then
                value +:= product_matrix[min][max];
            else
                value -:= product_matrix[min][max];
            end if;
        end for;
        image_null[num+1] := value;
    end for;
    return image_null;
end function;

// For a given theta null-point, return whether the corresponding abelian surface is isomorphic to the product of two elliptic curves or not.
function is_split(null)
    for j in [0,1,2,3,4,6,8,9,12,15] do
        if null[j+1] eq 0 then return true,j; end if;
    end for;
    return false;
end function;

// For a given theta null-point, return the j-invariants of two components of the corresponding abelian surface.
function restore_ellproduct(null)
    assert is_split(null) eq true;
    _, index := is_split(null);
    index_list := [split_table[1][index+1][num+1]: num in [0..15]]; sign_list := [split_table[2][index+1][num+1]: num in [0..15]];
    trans_null := transform_nullpoint(null,index_list,sign_list);
    t1 := trans_null[1]^2/(trans_null[1]^2-trans_null[2]^2); j1 := jInvariant(EllipticCurve(x*(x-1)*(x-t1)));
    t2 := trans_null[1]^2/(trans_null[1]^2-trans_null[3]^2); j2 := jInvariant(EllipticCurve(x*(x-1)*(x-t2))); inv := Sort([j1,j2]);
	return Sort([j1,j2]);
end function;

// For a given theta null-point, return a Rosenhain invariant of the corresponding genus-2 curve.
function restore_g2rosenhain(null)
    assert is_split(null) eq false;
    la := (null[1]*null[9])/(null[5]*null[13]);
    mu := (null[9]*null[3])/(null[13]*null[7]);
    nu := (null[3]*null[1])/(null[7]*null[5]);
    return la,mu,nu;
end function;

// Return a list of superspecial genus-2 curves with more than the given number of elements.
function listup_sspg2curve(limit)
    _, prod_null := generate_sspsurfnull(); null_set := [prod_null]; hyper_set := AssociativeArray(); step := 0;
    repeat
        step := step + 1; full_null := null_set[step];
        for j in [1..14] do // the 15th isogeny corresponds to the dual isogeny.
            index_list := [trans_table[1][j][num+1]: num in [0..15]]; sign_list := [trans_table[2][j][num+1]: num in [0..15]];
            trans_null := transform_nullpoint(full_null,index_list,sign_list);
            image_null := compute_twoisogeny(trans_null);
            if is_split(image_null) ne true then
                la,mu,nu := restore_g2rosenhain(image_null);
                inv := AbsoluteInvariants(HyperellipticCurve(x*(x-1)*(x-la)*(x-mu)*(x-nu)));
                if IsDefined(hyper_set,inv) ne true then
                    null_set := Append(null_set,image_null); hyper_set[inv] := [la,mu,nu];
                end if;
            end if;
        end for;
    until #hyper_set ge limit;
    return hyper_set;
end function;

// Return the lists of all edges and nodes in the (2,2)-isogeny graph of superspecial abelian surfaces.
function compute_sspg2graph()
    node_set := AssociativeArray(); edge_set := [];
    j, prod_null := generate_sspsurfnull(); null_set := [prod_null]; node_set[[j,j]] := 1; step := 0;
    repeat
        step := step + 1; full_null := null_set[step]; edges := {* *};
        for j in [1..15] do
            index_list := [trans_table[1][j][num+1]: num in [0..15]]; sign_list := [trans_table[2][j][num+1]: num in [0..15]];
            trans_null := transform_nullpoint(full_null,index_list,sign_list);
            image_null := compute_twoisogeny(trans_null);
            if is_split(image_null) ne true then
                la,mu,nu := restore_g2rosenhain(image_null);
                inv := AbsoluteInvariants(HyperellipticCurve(x*(x-1)*(x-la)*(x-mu)*(x-nu)));
            else
                inv := restore_ellproduct(image_null);
            end if;
            if IsDefined(node_set,inv) ne true then
                null_set := Append(null_set,image_null); node_set[inv] := #null_set;
            end if;
            edges := Include(edges,node_set[inv]);
        end for;
        edge_set[step] := edges;
    until step ge #null_set;
    return node_set, edge_set;
end function;