import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Complex.ExtAddA.eq.MulAS
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
  (χ ρ : Ch v δ)
  (u : UF v) :
-- imply
  chv (χ + ρ) u = chv χ u * chv ρ u :=
-- proof
  Complex.ExtAddA.eq.MulAS (A := Additive (Qm v δ)) χ ρ _

end LocalGL2.Kirillov

end


-- created on 2026-10-25
