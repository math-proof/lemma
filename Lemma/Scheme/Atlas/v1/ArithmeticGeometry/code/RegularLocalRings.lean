import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.ArithmeticGeometry.code.RegularLocalRings
open Order ValuationSubring


/--
[ValuationSubring.ringKrullDim_eq_coheight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularLocalRings.lean)
-/
@[path]
lemma ValuationSubring.ringKrullDim_eq_coheight
  [Field K]
  {R : ValuationSubring K} :
-- imply
  ringKrullDim R = coheight (α := ValuationSubring K) R := by
-- proof
  unfold ringKrullDim
  rw [← krullDim_orderDual, krullDim_eq_of_orderIso R.primeSpectrumOrderEquiv]
  exact (coheight_eq_krullDim_Ici R).symm

/--
[ValuationSubring.ringKrullDim_add_one_le_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularLocalRings.lean)
-/
@[path]
lemma ValuationSubring.ringKrullDim_add_one_le_of_lt
  [Field K]
  {R₁ R₂ : ValuationSubring K}
-- given
  (h : R₁ < R₂) :
-- imply
  ringKrullDim R₂ + 1 ≤ ringKrullDim R₁ := by
-- proof
  rw [R₁.ringKrullDim_eq_coheight, R₂.ringKrullDim_eq_coheight]
  exact_mod_cast coheight_add_one_le h

/--
[nakayama_lemma_18_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularLocalRings.lean)
-/
@[path]
lemma nakayama_lemma_18_3
  [Field K]
  [CommRing R]
  [IsLocalRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
-- given
  (h : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) = ⊤) :
-- imply
  Subsingleton M := by
-- proof
  have htop : (⊤ : Submodule R M) = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
    · exact Module.Finite.fg_top
    · rw [h]
    · rw [IsLocalRing.jacobson_eq_maximalIdeal]
      exact bot_ne_top
  rw [subsingleton_iff_forall_eq 0]
  intro x
  have hx : x ∈ (⊤ : Submodule R M) := Submodule.mem_top
  rw [htop] at hx
  exact (Submodule.mem_bot R).mp hx


-- created on 2026-10-23
