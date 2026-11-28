import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Syntax.LinearAlgebra.Matrix.Notation
import Syntax.LinearAlgebra.Matrix.Pow
import Lemma.Matrix.EqRotary01
import Lemma.Matrix.EqRotary'01
import Lemma.Matrix.InvRotary.eq.TRotary
import Lemma.Matrix.InvRotary'.eq.TRotary'
import Lemma.Matrix.MulDotMul__Rotary'.eq.Dot_MulRotary'Sub
import Lemma.Matrix.MulDotMul__Rotary.eq.Dot_MulRotarySub
import Lemma.Matrix.MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.StackAnd__DivSumSFin.of.Eq_1.All_Eq_Inv.All_EqDotS_Mul
import Lemma.Matrix.Rotary'Neg.eq.TRotary'
import Lemma.Matrix.RotaryNeg.eq.TRotary
open Fin Matrix Real
open scoped Matrix
set_option maxHeartbeats 800000


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
    MulDotMul__Rotary.eq.Dot_MulRotarySub (fun φ => (RotaryNeg.eq.TRotary φ).trans (InvRotary.eq.TRotary φ).symm) EqRotary01 Q K V

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
-- updated on 2026-11-28
