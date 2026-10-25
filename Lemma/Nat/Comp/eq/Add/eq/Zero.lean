import Mathlib
import sympy.Basic
import Notation.LocalGL2_Kirillov
import Def.LocalGL2_Kirillov
import Def.AutomorphicForm_ConstantTerm
import Instance.NumberField_Completion_Finite
import Instance.LocalGL2_Kirillov
import Lemma.Nat.Chv.eq.MulChvS
import Lemma.Nat.Rep.eq.Q
import Lemma.Complex.CardQmV.ne.Zero
import Lemma.Complex.Sum_ToChar.eq.Eq_0
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
  (ρ χ : Ch v δ) :
-- imply
  comp v δ (fun w => chv ρ w) χ = if χ + ρ = 0 then 1 else 0 := by
-- proof
  unfold comp
  have h : ∀ q : Qm v δ, chv χ (rep v δ q) • chv ρ (rep v δ q) = chv (χ + ρ) (rep v δ q) := by
    intro q
    rw [smul_eq_mul, Nat.Chv.eq.MulChvS]
  simp only [h]
  have h2 : ∑ q : Qm v δ, chv (χ + ρ) (rep v δ q) = ∑ a : Additive (Qm v δ), Ch.toChar (χ + ρ) a := by
    unfold chv
    simp only [Nat.Rep.eq.Q]
    exact Fintype.sum_equiv Additive.ofMul _ _ (fun _ => rfl)
  rw [h2, Complex.Sum_ToChar.eq.Eq_0]
  split_ifs
  · rw [smul_eq_mul, inv_mul_cancel₀ (Complex.CardQmV.ne.Zero v δ)]
  · simp

end LocalGL2.Kirillov

end


-- created on 2026-10-25
