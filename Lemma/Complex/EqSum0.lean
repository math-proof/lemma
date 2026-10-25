import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Instance.LocalGL2_Kirillov
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {A : Type*} [AddCommGroup A]

@[path]
private lemma main
  [Fintype A]
  {ψ : AddChar A ℂ}
-- given
  (hψ : ψ ≠ 0) :
-- imply
  ∑ a, ψ a = 0 := by
-- proof
  classical
  rw [AddChar.sum_eq_ite, if_neg hψ]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
