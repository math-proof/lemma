import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Int.VPow_N.eq.ExpNegN
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Int


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))

include hϖ in
@[path]
private lemma main
-- given
  (n : ℤ) :
-- imply
  Valued.v (((ϖ ^ n : Fx) : F)) ≠ 0 := by
-- proof
  rwa [Int.VPow_N.eq.ExpNegN v ϖ hϖ]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
