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

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
-- given
  (δ : Γ)
  (c : ℂ)
  (f : UF v → X)
  (χ : Ch v δ) :
-- imply
  comp v δ (fun w => c • f w) χ = c • comp v δ f χ := by
-- proof
  unfold comp
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => smul_comm (chv χ (rep v δ q)) c (f (rep v δ q))

end LocalGL2.Kirillov

end


-- created on 2026-10-25
