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
  (g : UF v → ℂ)
  (ξ : X)
  (χ : Ch v δ) :
-- imply
  comp v δ (fun w => g w • ξ) χ = comp v δ g χ • ξ := by
-- proof
  unfold comp
  rw [smul_assoc, Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun q _ => (smul_assoc _ _ _).symm

end LocalGL2.Kirillov

end


-- created on 2026-10-25
