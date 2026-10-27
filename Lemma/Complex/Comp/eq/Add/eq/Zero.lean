import Mathlib
import Initialize.Tactic.Attr.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.Comp
import Lemma.Nat.CompV.eq.Eq_0
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
  (c : ℂ)
  (χ : Ch v δ)
  (ξ : X)
  (γ : Ch v δ) :
-- imply
  comp v δ (fun u => (c * chv χ u) • ξ) γ = if γ + χ = 0 then c • ξ else 0 := by
-- proof
  have h : (fun u => (c * chv χ u) • ξ) = fun u => chv χ u • (c • ξ) := by
    funext u
    rw [smul_smul, mul_comm]
  rw [h, Nat.Comp, Nat.CompV.eq.Eq_0]

end LocalGL2.Kirillov

end


-- created on 2026-10-25
