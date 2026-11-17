module

public import Mathlib

public section


namespace NoetherianRings

/--
[hilbert_basis_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/NoetherianRings.lean)
-/
public theorem hilbert_basis_theorem
  {R : Type*}
  [CommRing R]
  [IsNoetherianRing R] :
-- imply
  IsNoetherianRing (Polynomial R) :=
-- proof
  Polynomial.isNoetherianRing

end NoetherianRings


-- created on 2026-10-23
