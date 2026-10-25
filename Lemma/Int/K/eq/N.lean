import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.VU.eq.One
import Lemma.Int.VPow_N.eq.ExpNegN
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Int


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

include hϖ in
@[path]
private lemma main
  {k n : ℤ}
  {δ : Γ}
  {u r : UF v}
-- given
  (hδ : δ ≤ 1)
  (h : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) <
      (δ : WithZero (Multiplicative ℤ)) * Valued.v (((ϖ ^ n : Fx) : F))) :
-- imply
  k = n := by
-- proof
  have hδ' : (δ : WithZero (Multiplicative ℤ)) ≤ 1 := Units.val_le_val.mpr hδ
  have hvn : Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) = Valued.v (((ϖ ^ n : Fx) : F)) := by
    rw [Units.val_mul, map_mul, Nat.VU.eq.One, mul_one]
  have hvk : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F)) = Valued.v (((ϖ ^ k : Fx) : F)) := by
    rw [Units.val_mul, map_mul, Nat.VU.eq.One, mul_one]
  have hlt : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) <
      Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) := by
    rw [hvn]
    refine h.trans_le ?_
    calc
      _ ≤ 1 * Valued.v (((ϖ ^ n : Fx) : F)) := mul_le_mul_left hδ' _
      _ = _ := one_mul _
  have heq : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F)) = Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) := by
    have e : ((ϖ ^ k * (u : Fx) : Fx) : F) =
        (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) + ((ϖ ^ n * (r : Fx) : Fx) : F) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ hlt]
  rw [hvk, hvn, Int.VPow_N.eq.ExpNegN v ϖ hϖ, Int.VPow_N.eq.ExpNegN v ϖ hϖ] at heq
  exact neg_injective (WithZero.exp_injective heq)

end LocalGL2.Kirillov

end


-- created on 2026-10-25
