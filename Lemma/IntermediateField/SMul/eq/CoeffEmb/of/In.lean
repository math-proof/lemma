import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.ArithmeticGalois
import Lemma.Int.P2MUtil

open ModularCurve AlgebraicCurve IntermediateField HahnSeries

/--
[ModularCurve_arithmeticGalois_smul_coeffEmb](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_arithmeticGalois_smul_coeffEmb.lean)
-/
@[path]
private lemma main
  [Field L] [Algebra ℚ L]
  {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
  {x : LaurentSeries ℚ}
-- given
  (σ : L ≃ₐ[ℚ] L)
  (hx : x ∈ F₀) :
-- imply
  ModularCurve.arithmeticGalois F₀ σ • (⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ : ModularCurve.laurentBaseChange L F₀) = ⟨ModularCurve.coeffEmb L x, ModularCurve.coeffEmb_mem_laurentBaseChange L hx⟩ := by
-- proof
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul]
  exact coeffMap_coeffEmb σ x


-- created on 2026-10-23
