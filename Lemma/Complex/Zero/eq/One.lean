import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {A : Type*} [AddCommGroup A]

@[path]
private lemma main
-- given
  (ψ : AddChar A ℂ) :
-- imply
  ψ 0 = 1 :=
-- proof
  AddChar.map_zero_eq_one ψ

end LocalGL2.Kirillov

end


-- created on 2026-10-25
