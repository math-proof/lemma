import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Fin.Dg.eq.A
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Fin


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path]
private lemma main:
-- imply
  dg v 1 = 1 := by
-- proof
  apply Units.ext
  simp only [Fin.Dg.eq.A, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end LocalGL2.Kirillov

end


-- created on 2026-10-25
