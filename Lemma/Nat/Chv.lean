import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.ExtNegA.eq.A
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
  (χ : Ch v δ)
  (u : UF v) :
-- imply
  chv (-χ) u = (chv χ u)⁻¹ :=
-- proof
  Complex.ExtNegA.eq.A (A := Additive (Qm v δ)) χ _

end LocalGL2.Kirillov

end


-- created on 2026-10-25
