import Mathlib
import Initialize.Tactic.Attr.Basic
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
  {ψ φ : AddChar A ℂ}
-- given
  (h : ∀ a : A, ψ a = φ a) :
-- imply
  ψ = φ :=
-- proof
  AddChar.ext ψ φ h

end LocalGL2.Kirillov

end

-- created on 2026-10-25
