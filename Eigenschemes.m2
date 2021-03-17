-- The functions isEigenscheme and isEigenschemeSymmetric test whether a given set of points P in P^2 is the eigenscheme of a partially symmetric and symmetric tensor of order d.

loadPackage("Points")

-- P is a nx3 matrix with rational entries, d\geq 2 is a positive integer and R is QQ[x0,x1,x2]
isEigenscheme = (P,d,R) -> (
	(I,G) := projectivePoints(P,R);
	return isIdealEigenscheme(ideal(G),d)
)

isEigenschemeSymmetric = (P,d,R) -> (
	(I,G) := projectivePoints(P,R);
	return isIdealEigenschemeSymmetric(ideal(G),d)
)

isIdealEigenscheme = (I,d) -> (
	if degree I != d^2-d+1 then error "The number of points must be equal to d^2-d+1";
	if hilbertFunction(d,module(I))!=3 then return false;
	R := ring(I);
	S := QQ[y00,y01,y02,y10,y11,y12,y20,y21,y22][x0,x1,x2];
	ringmap := map(S,R);
	J := ringmap(I);
	B := res J;
	L := (select(entries transpose B.dd_2, i-> (degree(i#0)#0)#0==1 ))#0;
	H := (select(entries transpose B.dd_2, i-> (degree(i#0)#0)#0==d-1 ))#(-1);
	A := matrix({{diff(x0,L#0),diff(x1,L#0),diff(x2,L#0)},{diff(x0,L#1),diff(x1,L#1),diff(x2,L#1)},{diff(x0,L#2),diff(x1,L#2),diff(x2,L#2)}});
	use R;
	if determinant A == 0 then return {false}
	else return {true,inverse(A)*transpose(matrix({H}))}
)

isIdealEigenschemeSymmetric = (I,d) -> (
	T1 := isIdealEigenscheme(I,d);
	if T1#0 == false then return false
	--else return inverse(A)*transpose(matrix({H}))
	--else return matrix({{x1*H#2-x2*H#1,x0*H#2-x2*H#0,x0*H#1-x1*H#0}})
	else( AH := flatten entries((isIdealEigenscheme(I,d))#1) );
	S := ring(AH#0);
	use(S);
	Q := {x1*AH#2-x2*AH#1,x0*AH#2-x2*AH#0,x0*AH#1-x1*AH#0};
	if diff(x0,Q#0)-diff(x1,Q#1)+diff(x2,Q#2) == 0 then(return {true,reconstructSymmetricTensor(AH,d, ring I)} )
	else( use ring I; 
	    return false)
)

reconstructSymmetricTensor = (AH,d,R) -> (
	Rnew := QQ[c_1..c_(binomial(d+2,2)),k_1..k_(binomial(d,2))][x0,x1,x2];
	Rt := QQ[x0,x1,x2];
	map1 := map(Rt,ring(AH#0));
	map2 := map(Rnew,Rt);
	(g0,g1,g2) := (map2(map1(AH#0)), map2(map1(AH#1)), map2(map1(AH#2)));
	use Rnew;
	Md := flatten entries gens((ideal(x0,x1,x2))^(d)) ;
	Mdm3 := flatten entries gens((ideal(x0,x1,x2))^(d-1));
	Mdm2 := flatten entries gens((ideal(x0,x1,x2))^(d-2)) ;
	f := sum(toList apply((0..binomial(d+2,2)-1), i-> c_(i+1)*Md#i)); 
	h := sum(toList apply((0..binomial(d,2)-1), i-> k_(i+1)*Mdm2#i));
	R4 := apply(Mdm3, i-> coefficient(i,diff(x0,f)-g0-x0*h)); 
	R5 := apply(Mdm3, i-> coefficient(i,diff(x1,f)-g1-x1*h)); 
	R6 := apply(Mdm3, i-> coefficient(i,diff(x2,f)-g2-x2*h)); 
	R7 := R4|R5|R6;
	map3 := map(QQ,ring(R7#0));
	AA := matrix(toList apply(R7, l-> toList apply(gens ring(R7#0), i-> promote(coefficient(i,l),QQ))) );
	BB := matrix({toList apply(R7, l-> -map3(part(0,l)) )});
	XX := solve(AA,transpose BB);
	ftilde := sum(toList apply((0..binomial(d+2,2)-1), i-> ((flatten entries XX)#i) * Md#i));
	map4 := map(R, ring(ftilde));
	use R;
	return(map4(ftilde))
)    
