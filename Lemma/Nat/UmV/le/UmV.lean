import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Int


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
  {δ δ₁ : Γ}
-- given
  (h : δ ≤ δ₁) :
-- imply
  Um v δ ≤ Um v δ₁ :=
-- proof
  fun m hm =>
  ((Int.U.in.UmV.is.UFnSub.lt.WithZero_Multiplicative v δ m).mp hm).trans_le (Units.val_le_val.mpr h)

end LocalGL2.Kirillov

end


-- created on 2026-10-25
