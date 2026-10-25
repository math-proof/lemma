/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BellMatrix.lean -/

import Mathlib.RingTheory.PowerSeries.Basic
/-!
# Bell matrices

A Bell matrix is the Riordan array `(g(X), X * g(X))`. The source works over integer power
series normalized by `g(0) = 1`; here this is generalized to power series over a commutative ring
whose constant coefficient is a unit, the usual condition needed for a ring-valued Riordan array.

Source: Paul Barry, *On the Central Coefficients of Bell Matrices*,
<https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry3/barry132.tex>.

JIS concept: `jis_sem_70c33473bf189e979a585e79`.
-/


namespace MetaMathlibExt

/-- The data determining a Bell matrix: a power series `g` with invertible constant coefficient.
The corresponding Riordan-array pair is `(g, X * g)`. -/
structure BellMatrix (R : Type*) [CommRing R] where
  g : PowerSeries R
  isUnit_const : IsUnit g.constantCoeff

end MetaMathlibExt
