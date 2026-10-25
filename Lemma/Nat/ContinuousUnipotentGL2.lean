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

@[path]
private lemma main:
-- imply
  Continuous (fun x : F => (unipotentGL2 x : G)) := by
-- proof
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

end LocalGL2.Kirillov

end


-- created on 2026-10-25
