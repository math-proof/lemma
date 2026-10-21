import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial
open scoped nonZeroDivisors


/--
[rothIntPolynomial_isRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ) :
-- imply
  eval α ((rothIntPolynomial α).map (algebraMap ℤ ℝ)) = 0 := by
-- proof
  obtain ⟨b, hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec ℤ⁰ (minpoly ℚ α)
  change
    eval α
      ((IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α)).map
        (algebraMap ℤ ℝ)) = 0
  have hmap : algebraMap ℤ ℝ = (algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ) := by
    ext
    simp
  have hmapsmul :
    map (algebraMap ℚ ℝ) (b • minpoly ℚ α) =
      b • map (algebraMap ℚ ℝ) (minpoly ℚ α) :=
    map_zsmul (mapRingHom (algebraMap ℚ ℝ)) b (minpoly ℚ α)
  have hroot : eval₂ (algebraMap ℚ ℝ) α (minpoly ℚ α) = 0 := by
    rw [← aeval_def]
    exact minpoly.aeval ℚ α
  rw [hmap, ← map_map, hspec, hmapsmul, eval_smul]
  simp [eval_map, hroot]


-- created on 2026-10-21
