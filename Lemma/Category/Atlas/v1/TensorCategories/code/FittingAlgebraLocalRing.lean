import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.FittingAlgebraLocalRing


/--
[mulRight_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FittingAlgebraLocalRing.lean)
-/
@[path]
private lemma mulRight_pow_eq
  [CommSemiring k]
  [Ring R]
  [Algebra k R]
  {a : R}
  {n : ℕ} :
-- imply
  (LinearMap.mulRight k a) ^ n = LinearMap.mulRight k (a ^ n) := by
-- proof
  apply mulRight_pow a n

/--
[isLocalRing_of_finiteDimensional_of_no_nontrivial_idempotents](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FittingAlgebraLocalRing.lean)
-/
@[path]
private lemma isLocalRing_of_finiteDimensional_of_no_nontrivial_idempotents_eq
  {k : Type*}
  [Field k]
  {R : Type*}
  [Ring R]
  [Nontrivial R]
  [Algebra k R]
  [FiniteDimensional k R]
-- given
  (h_idem : ∀ e : R, e * e = e → e = 0 ∨ e = 1) :
-- imply
  IsLocalRing R := by
-- proof
  apply isLocalRing_of_finiteDimensional_of_no_nontrivial_idempotents k R h_idem


-- created on 2026-10-23
