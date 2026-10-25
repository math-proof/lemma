import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Instance.LocalGL2_Kirillov
import Lemma.Complex.Sum.eq.CardA
import Lemma.Complex.EqSum0
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
  (χ : Ch v δ) :
-- imply
  ∑ a : Additive (Qm v δ), Ch.toChar χ a = if χ = 0 then (Fintype.card (Qm v δ) : ℂ) else 0 := by
-- proof
  rw [Fintype.card_congr (Additive.ofMul : Qm v δ ≃ Additive (Qm v δ))]
  split_ifs with h
  · exact Complex.Sum.eq.CardA (A := Additive (Qm v δ)) (by rw [h]; rfl)
  · exact Complex.EqSum0 (A := Additive (Qm v δ)) h

end LocalGL2.Kirillov

end


-- created on 2026-10-25
