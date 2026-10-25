import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Instance.LocalGL2_Kirillov
import Lemma.Complex.Sum.eq.Card
import Lemma.Complex.Sum.eq.Zero
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {v} in
@[path]
private lemma main
  {δ : Γ}
-- given
  (u : UF v) :
-- imply
  ∑ χ : Ch v δ, chv χ u = if (u : Qm v δ) = 1 then (Fintype.card (Qm v δ) : ℂ) else 0 := by
-- proof
  unfold chv
  rw [Fintype.card_congr (Additive.ofMul : Qm v δ ≃ Additive (Qm v δ))]
  split_ifs with h
  · exact Complex.Sum.eq.Card (A := Additive (Qm v δ)) (ofMul_eq_zero.mpr h)
  · exact Complex.Sum.eq.Zero (A := Additive (Qm v δ)) (fun h' => h (ofMul_eq_zero.mp h'))

end LocalGL2.Kirillov

end


-- created on 2026-10-25
