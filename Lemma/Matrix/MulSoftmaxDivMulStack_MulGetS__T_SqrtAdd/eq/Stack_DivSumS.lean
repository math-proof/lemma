import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Syntax.LinearAlgebra.Matrix.Notation
import Syntax.LinearAlgebra.Matrix.Pow
import Lemma.Fin.Any_In_BraceCastAdd__NatAdd
import Lemma.Fin.CastAdd.ne.NatAdd
import Lemma.Fin.InjectiveNatAdd
import Lemma.Matrix.EqRotary01
import Lemma.Matrix.EqRotary'01
import Lemma.Matrix.InvRotary'.eq.TRotary'
import Lemma.Matrix.InvRotaryOn.eq.TRotaryOn.of.All_EqSum__Add.All_Any_In_Brace.All_Ne.Injective.Injective
import Lemma.Matrix.MulDotMul__Rotary'.eq.Dot_MulRotary'Sub
import Lemma.Matrix.MulDotMul__Rotary.eq.Dot_MulRotarySub
import Lemma.Matrix.MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
import Lemma.Matrix.Rotary'Neg.eq.TRotary'
import Lemma.Real.Sum.eq.Add_Sum
import Lemma.Fin.Sum_IteAnd
open Fin Matrix Real
open scoped Matrix
set_option maxHeartbeats 800000


private lemma rotaryOn_neg
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (θ : Fin d → ℝ) :
-- imply
  Matrix.rotaryOn u v (-θ) = (Matrix.rotaryOn u v θ)ᵀ := by
-- proof
  ext i j
  have hL :
    Matrix.rotaryOn u v (-θ) i j =
      (∑ t : Fin d, if i = u t ∧ j = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if i = u t ∧ j = v t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = u t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if i = v t ∧ j = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.rotaryOn, Matrix.of_apply, Pi.neg_apply, Finset.sum_add_distrib, Real.cos_neg,
      Real.sin_neg, neg_neg]
  have hR :
    (Matrix.rotaryOn u v θ)ᵀ i j =
      (∑ t : Fin d, if j = u t ∧ i = u t then Real.cos (θ t) else 0) +
      (∑ t : Fin d, if j = u t ∧ i = v t then -Real.sin (θ t) else 0) +
      (∑ t : Fin d, if j = v t ∧ i = u t then Real.sin (θ t) else 0) +
      (∑ t : Fin d, if j = v t ∧ i = v t then Real.cos (θ t) else 0) := by
    simp only [Matrix.transpose_apply, Matrix.rotaryOn, Matrix.of_apply, Finset.sum_add_distrib]
  rw [hL, hR]
  rw [Sum_IteAnd (p := fun t => i = u t) (q := fun t => j = u t) (f := fun t => Real.cos (θ t))]
  rw [Sum_IteAnd (p := fun t => i = u t) (q := fun t => j = v t) (f := fun t => Real.sin (θ t))]
  rw [Sum_IteAnd (p := fun t => i = v t) (q := fun t => j = u t) (f := fun t => -Real.sin (θ t))]
  rw [Sum_IteAnd (p := fun t => i = v t) (q := fun t => j = v t) (f := fun t => Real.cos (θ t))]
  ring

private lemma rotary_neg
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  Matrix.rotary (-φ) = (Matrix.rotary φ)ᵀ := by
-- proof
  simpa [Matrix.rotary] using rotaryOn_neg (u := Fin.castAdd d) (v := Fin.natAdd d) φ

private lemma rotary_inv
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotary φ)⁻¹ = (Matrix.rotary φ)ᵀ := by
-- proof
  simpa [Matrix.rotary] using
    InvRotaryOn.eq.TRotaryOn.of.All_EqSum__Add.All_Any_In_Brace.All_Ne.Injective.Injective (Fin.castAdd_injective d d)
      (InjectiveNatAdd d) CastAdd.ne.NatAdd Any_In_BraceCastAdd__NatAdd
      (Sum.eq.Add_Sum (d := d)) φ

/--
Rotary attention collapses to relative angles when each frequency row is linear in the token index.

The usual schedule is `θ[i][j] = λ * i / b ^ (j / d)`. Here that is weakened to `θ[i][j] = τ j * i`.
`Matrix.rotary` is the half-split rotation, with planes `(j, j + d)`.
-/
@[path]
private lemma main
  {n d : ℕ}
  {τ : Fin d → ℝ}
-- given
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let θ := [i < n] ((i : ℝ) • τ)
  let R (i : Fin n) := θ[i].rotary
  let Rₑ (i k : Fin n) :=
    R[(k - i : ℤ).natAbs] ^ (k - i : ℤ).sign
  (([i < n] (R[i] *ᵥ Q[i])) *
      ([i < n] (R[i] *ᵥ K[i]))ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n][j < d + d]
      (∑ k : Fin n, V[k][j] * (Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ)).exp) /
        ∑ k : Fin n,
          (R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ)).exp := by
-- proof
  apply MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
    MulDotMul__Rotary.eq.Dot_MulRotarySub (fun φ => (rotary_neg φ).trans (rotary_inv φ).symm) EqRotary01 Q K V

/-- Adjacent-pair form of the same identity. `Matrix.rotary'` rotates planes `(2j, 2j + 1)`. -/
@[path]
private lemma interleave
  {n d : ℕ}
  {τ : Fin d → ℝ}
-- given
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let θ := [i < n] ((i : ℝ) • τ)
  let R (i : Fin n) := θ[i].rotary'
  let Rₑ (i k : Fin n) :=
    R[(k - i : ℤ).natAbs] ^ (k - i : ℤ).sign
  (([i < n] (R[i] *ᵥ Q[i])) *
      ([i < n] (R[i] *ᵥ K[i]))ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n][j < d + d]
      (∑ k : Fin n, V[k][j] * (Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ)).exp) /
        ∑ k : Fin n,
          (R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ)).exp := by
-- proof
  apply MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
    MulDotMul__Rotary'.eq.Dot_MulRotary'Sub (fun φ => (Rotary'Neg.eq.TRotary' φ).trans (InvRotary'.eq.TRotary' φ).symm) EqRotary'01 Q K V


-- created on 2023-06-09
-- updated on 2026-11-27
