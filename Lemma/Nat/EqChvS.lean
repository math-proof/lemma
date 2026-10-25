import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.Chv.eq.F
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
  {δ δ₁ : Γ}
-- given
  (h : δ ≤ δ₁)
  (τ : Ch v δ₁)
  (u : UF v) :
-- imply
  chv (refineCh v h τ) u = chv τ u :=
-- proof
  Complex.Chv.eq.F v δ _ _ _ u

end LocalGL2.Kirillov

end


-- created on 2026-10-25
