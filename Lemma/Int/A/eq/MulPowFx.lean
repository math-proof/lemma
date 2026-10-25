import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Int.VPow_N.eq.ExpNegN
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Int


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

include hϖ in
@[path]
private lemma main
-- given
  (a : Fx) :
-- imply
  ∃ (k : ℤ) (u : UF v), a = ϖ ^ k * (u : Fx) := by
-- proof
  have hva : Valued.v (a : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  set k : ℤ := -WithZero.log (Valued.v (a : F)) with hk
  have hvk : Valued.v (((ϖ ^ k : Fx) : F)) = Valued.v (a : F) := by
    rw [Int.VPow_N.eq.ExpNegN v ϖ hϖ, hk, neg_neg, WithZero.exp_log hva]
  refine ⟨k, ⟨(ϖ ^ k)⁻¹ * a, ?_⟩, (mul_inv_cancel_left (ϖ ^ k) a).symm⟩
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvk, inv_mul_cancel₀ hva]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
