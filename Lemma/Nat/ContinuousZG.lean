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
  Continuous (fun c : Fx => (zG v c : G)) := by
-- proof
  have hφ : Continuous (fun a : F => !![a, 0; 0, a]) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  rw [Units.continuous_iff]
  exact ⟨hφ.comp Units.continuous_val, hφ.comp Units.continuous_coe_inv⟩

end LocalGL2.Kirillov

end


-- created on 2026-10-25
