# coherence

Consider two terms of the same type, say `t` and `t'`, in a simply typed lambda calculus with 
unit, products and functions. 
How do we decide if they are equal?
We could, for instance, evaluate (normalize) the terms to check whether they produce the same result 
(normal forms), and if they do, we can deem them equal.

In this specific calculus, however, there is no need to normalize terms 
since any two terms of the same type are always equal!
This means that deciability in this calculus is trivially 
a "yes" for two terms of the same type.
This simple property can be proved as a trivial case of the coherence theorem for CCCs.

In most presentations of the CCC coherence theorem, one needs to squint a bit to see 
this property of decidability (since it includes the more interesting base types),
so I decided to prove it in isolation. 
