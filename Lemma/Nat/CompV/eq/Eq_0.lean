import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Lemma.Nat.Chv_0U.eq.One
import Lemma.Nat.Comp.eq.Add.eq.Zero
import Lemma.Complex.CompEqSMul
open scoped Classical LocalGL2_Kirillov
open AutomorphicForm IsDedekindDomain NumberField
open Nat
open Complex


noncomputable section

namespace LocalGL2.Kirillov

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

@[path]
private lemma main
-- given
  (δ : Γ)
  (ξ : X)
  (γ : Ch v δ) :
-- imply
  comp v δ (fun _ : UF v => ξ) γ = if γ = 0 then ξ else 0 := by
-- proof
  have h : (fun _ : UF v => ξ) = fun u => chv (0 : Ch v δ) u • ξ := by
    funext u
    rw [Nat.Chv_0U.eq.One, one_smul]
  rw [h, Complex.CompEqSMul, Nat.Comp.eq.Add.eq.Zero, add_zero]
  split_ifs <;> simp

end LocalGL2.Kirillov

end


-- created on 2026-10-25
