# coherence

Consider a simply typed lambda calculus with unit, products and functions. 
In this calculus, how do we decide if two terms of the same type are equal? 
Typically, we would evaluate (normalize) the terms to check whether they produce the same result (normal forms), and if they do, we can deem them equal. In this *specific* calculus, however, there is no need to normalize terms 
because of the following property: 


**Any two terms of the same type are equal, i.e., for Γ ⊢ t t' : a, we have that t ~ t'**

where ~ is the standard beta-eta equivalence.

This property means that deciability (of equality) for two terms of the same type is trivially  a "yes".
This property can be proved as a trivial case of the coherence theorem for CCCs.
In most presentations of the CCC coherence theorem [1] [2], one needs to squint a bit to see 
this property of decidability (since it considers a more expressive calculus),
so I decided to prove it in isolation.


References
* [1] Babaev, A. A., and S. V. Solov'ev. "A coherence theorem for canonical morphisms in cartesian closed categories." Journal of Soviet Mathematics 20.4 (1982): 2263-2279.
* [2] Troelstra, Anne Sjerp, and Helmut Schwichtenberg. Basic proof theory. No. 43. Cambridge University Press, 2000.
