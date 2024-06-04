
-- -*- coding: utf-8 -*-
newPackage(
    "ParametricGroebnerBases",
    Version => "0.1",
    Date => "June 5, 2024",
    Authors => {
	{Name => "Andreas Bøgh Poulsen", Email => "doe@math.uiuc.edu", HomePage => "http://www.math.uiuc.edu/~doe/"}},
    Headline => "A package for computing and working with parametric Gröbner bases, Gröbner systems and Gröbner covers",
    Keywords => {"Gröbner Bases, Gröbner, Grobner, Groebner, parametric, comprehensive Gröbner bases"},
    DebuggingMode => false
    )

export {"firstFunction"}


CGS = method();
CGS(Ideal, Ideal) := (I, S) -> (
  if (1 % S == 0) then return {{}};
  G := gb (ideal ((entries gens I)#0 | (entries gens S)#0));
  Gs := select((entries gens G)#0, f -> (leadCoefficient(f) % S) != 0);

  hs := apply(Gs, leadCoefficient);
  
  if (hs == {}) then return {{ideal gens gb S, ideal 1, Gs}};
  h := fold(lcm, hs);

  return {{ideal gens gb S, ideal h, Gs}} | 
    fold((l1, l2) -> l1 | l2, 
         apply(hs, hx -> CGS(I, S + (ideal hx))));
);
CGS(Ideal) :=  I -> (
  G := gb I;
  S := ideal select((entries(gens G))#0, f -> 0 == first degree f);

  return {{ideal 0, S, {1}}} | CGS(I, S);
);

pseudoRemainder(RingElement, List) := (f, G) -> (
  f' := f;
  r := 0_(ring(f));
  c := 1_(baseRing(ring(f)));

  while (not zero(f')) do (
    t := leadTerm(f');
    a := leadCoefficient(f');
    m := leadMonomial(f');
    G' := select(G, g -> m % leadMonomial(g) == 0);
    if (G' == {}) then (
      r = r + t;
      f' = f' - t;
    ) else (
      g := first G';
      c = c*leadCoefficient(g);
      r = r*leadCoefficient(g);
      gam := m // leadMonomial(g);
      f' = leadCoefficient(g)*f' - gam*leadCoefficient(f')*g;
    );
  );
  return r;
)
pseudoRemainder(RingElement, Ideal) := (f, G) -> (
  return pseudoRemainder(f, (entries gens G)#0)
)

interReduce = method()
interReduce (List) := G -> (
  G' := new MutableList from G;
  for i from 0 to (length(G)-1) do (
    r := pseudoRemainder(G'#i, (toList G')_{0..(i-1)} | (toList G')_{(i+1)..(length(G)-1)});
    G'#i = r;
  );
  return toList select(G', g -> not zero(g));
)

beginDocumentation()

doc ///
 Node
  Key
   FirstPackage
  Headline
     an example Macaulay2 package
  Description
   Text
    {\em FirstPackage} is a basic package to be used as an example.
  Caveat
    Still trying to figure this out.
  Subnodes
    firstFunction
 Node
  Key
   (firstFunction,ZZ)
   firstFunction
  Headline
   a silly first function
  Usage
   firstFunction n
  Inputs
   n:
  Outputs
   :
    a silly string, depending on the value of {\tt n}
  Description
   Text
    Here we show an example.
   Example
    firstFunction 1
    firstFunction 0
///

TEST ///
    assert ( firstFunction 2 == "D'oh!" )
///

end--

You can write anything you want down here.  I like to keep examples
as I’m developing here.  Clean it up before submitting for
publication.  If you don't want to do that, you can omit the "end"
above.
