import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.Chv.eq.MulChvS
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
-- given
  (δ : Γ)
  (ρ : Ch v δ)
  (f : UF v → X)
  (χ : Ch v δ) :
-- imply
  comp v δ (fun w => chv ρ w • f w) χ = comp v δ f (χ + ρ) := by
-- proof
  unfold comp
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, Nat.Chv.eq.MulChvS]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
