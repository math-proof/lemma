import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Fin.Dg.eq.A
import Lemma.Fin.WGCoe
import Lemma.Fin.ZG.eq.C
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Fin


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

@[path]
private lemma main
-- given
  (a : Fx) :
-- imply
  dg v a * wG v = wG v * zG v a * dg v a⁻¹ := by
-- proof
  apply Units.ext
  simp only [Units.val_mul, Fin.Dg.eq.A, Fin.WGCoe, Fin.ZG.eq.C]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
