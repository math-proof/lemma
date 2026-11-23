import Def.Analysis.Matrix.Softmax
import Def.LinearAlgebra.Matrix.Rotary
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.SpecialFunctions.Exponential
import Instance.LinearAlgebra.Matrix.Div
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Syntax.LinearAlgebra.Matrix.Notation
import Syntax.LinearAlgebra.Matrix.Pow
import Instance.Data.Fin.Fun
import Instance.LinearAlgebra.Matrix.GetElem
import Instance.LinearAlgebra.Matrix.SignPow
open Matrix Real
open scoped Matrix


/-- If each frequency row is linear in the token index, its entries are scalar multiples of the base row. -/
private lemma theta_apply
  {n d : ℕ}
  {θ : ℝ ^ [n, d]}
  {τ : Fin d → ℝ}
-- given
  (hθ : θ = [i < n] ((i : ℝ) • τ))
  (p : Fin n)
  (t : Fin d) :
-- imply
  θ p t = τ t * (p : ℝ) := by
-- proof
  simp [hθ, Pi.smul_apply]
  ring

/-- The rotation of a difference of two such rows is a signed power of the rotation at the absolute index difference. -/
private lemma rel_linear
  {n d : ℕ}
  {θ : ℝ ^ [n, d]}
  {τ : Fin d → ℝ}
  {ℛ : (Fin d → ℝ) → ℝ ^ [d + d, d + d]}
-- given
  (hθ : θ = [i < n] ((i : ℝ) • τ))
  (h : ∀ φ, ℛ (-φ) = (ℛ φ)⁻¹)
  (hzero : ℛ 0 = 1)
  (i k : Fin n) :
-- imply
  ℛ ((θ[k] - θ[i])) =
    ℛ (θ[(⟨(k - i : ℤ).natAbs, by omega⟩ : Fin n)] : Fin d → ℝ) ^
      (k - i : ℤ).sign := by
-- proof
  if hlt : (k : ℕ) < (i : ℕ) then
    have hsign : (k - i : ℤ).sign = -1 := by
      apply Int.sign_eq_neg_one_of_neg
      omega
    have hle : (k : ℕ) ≤ (i : ℕ) := Nat.le_of_lt hlt
    have habs : (k - i : ℤ).natAbs = (i : ℕ) - (k : ℕ) := by
      have hsub : (k - i : ℤ) = -(i - k : ℤ) := by ring
      rw [hsub, Int.natAbs_neg]
      have hcoe (p : Fin n) : (p : ℤ) = ((p : ℕ) : ℤ) := by simp
      rw [hcoe i, hcoe k, (Int.ofNat_sub hle).symm]
      simp
    rw [hsign]
    rw [show ℛ (θ[(⟨(k - i : ℤ).natAbs, by omega⟩ : Fin n)] : Fin d → ℝ) ^ (-1 : ℤ) =
        Matrix.signPow (A := ℛ (θ[(⟨(k - i : ℤ).natAbs, by omega⟩ : Fin n)] : Fin d → ℝ)) (-1) from rfl]
    simp [Matrix.signPow]
    rw [← h]
    apply congrArg
    funext t
    simp only [Pi.sub_apply, Pi.neg_apply, theta_apply hθ]
    rw [show (k - i : ℤ).natAbs = (i : ℕ) - (k : ℕ) from habs]
    rw [Nat.cast_sub hle]
    ring
  else if heq : (k : ℕ) = (i : ℕ) then
    have hsign : (k - i : ℤ).sign = 0 := by
      have hsub : (k : ℤ) - (i : ℤ) = 0 := by omega
      simp [hsub]
    rw [hsign]
    change _ = (1 : ℝ ^ [d + d, d + d])
    rw [← hzero]
    apply congrArg
    funext t
    simp only [Pi.sub_apply, Pi.zero_apply, getElem_apply, theta_apply hθ, heq]
    ring
  else
    have hgt : (i : ℕ) < (k : ℕ) := by
      omega
    have hle : (i : ℕ) ≤ (k : ℕ) := Nat.le_of_lt hgt
    have hsign : (k - i : ℤ).sign = 1 := by
      apply Int.sign_eq_one_of_pos
      omega
    have habs : (k - i : ℤ).natAbs = (k : ℕ) - (i : ℕ) := by
      omega
    rw [hsign]
    rw [show ℛ (θ[(⟨(k - i : ℤ).natAbs, by omega⟩ : Fin n)] : Fin d → ℝ) ^ (1 : ℤ) =
        Matrix.signPow (A := ℛ (θ[(⟨(k - i : ℤ).natAbs, by omega⟩ : Fin n)] : Fin d → ℝ)) 1 from rfl]
    simp [Matrix.signPow]
    apply congrArg
    funext t
    simp only [Pi.sub_apply, theta_apply hθ]
    rw [show (k - i : ℤ).natAbs = (k : ℕ) - (i : ℕ) from habs]
    rw [Nat.cast_sub hle]
    ring

/--
Rotary attention collapses to relative angles for any rotation family that preserves the rotated dot product,
sends zero to the identity, and sends negation to the inverse.
-/
@[path]
private lemma main
  {n d : ℕ}
  {τ : Fin d → ℝ}
  {ℛ : (Fin d → ℝ) → ℝ ^ [d + d, d + d]}
-- given
  (hdot : ∀ (α β : Fin d → ℝ) (q k : Fin (d + d) → ℝ),
    ℛ α *ᵥ q ⬝ᵥ ℛ β *ᵥ k =
      q ⬝ᵥ ℛ (β - α) *ᵥ k)
  (h : ∀ φ, ℛ (-φ) = (ℛ φ)⁻¹)
  (hzero : ℛ 0 = 1)
  (Q K V : ℝ ^ [n, d + d]) :
-- imply
  let θ := [i < n] ((i : ℝ) • τ)
  let R (i : Fin n) := ℛ θ[i]
  let Rₑ (i k : Fin n) :=
    R[(k - i : ℤ).natAbs] ^ (k - i : ℤ).sign
  (([i < n] (R[i] *ᵥ Q[i])) *
      ([i < n] (R[i] *ᵥ K[i]))ᵀ / √(d + d : ℝ)).softmax * V =
    [i < n][j < d + d]
      (∑ k : Fin n, V[k][j] * (Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ)).exp) /
        ∑ k : Fin n,
          (R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ)).exp := by
-- proof
  intro θ R Rₑ
  ext i j
  simp only [Matrix.ofFun_apply]
  let RQ : ℝ ^ [n, d + d] := [p < n] (R[p] *ᵥ Q[p])
  let RK : ℝ ^ [n, d + d] := [p < n] (R[p] *ᵥ K[p])
  let S : ℝ ^ [n, n] := RQ * RKᵀ / √(d + d : ℝ)
  have hRQ (p : Fin n) : RQ p = R[p] *ᵥ Q[p] := by
    ext j
    simp [RQ]
  have hRK (p : Fin n) : RK p = R[p] *ᵥ K p := by
    ext j
    simp [RK]
  have hS : (([p < n] (R[p] *ᵥ Q[p])) *
      ([p < n] (R[p] *ᵥ K[p]))ᵀ / √(d + d : ℝ)) = S := by
    simp [S, RQ, RK]
  rw [hS]
  have hsm (k : Fin n) :
    (S.softmax) i k = (S i k).exp / ∑ k' : Fin n, (S i k').exp := by
    unfold Matrix.softmax
    rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0)]
    rw [ite_eq_left (by decide : (1 : ℕ) = 1)]
    simp [Matrix.of_apply]
    rfl
  have hprod (k : Fin n) : (RQ * RKᵀ) i k = RQ i ⬝ᵥ RK k := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  have hentry (k : Fin n) :
    S i k = R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ) := by
    simp [S, Matrix.div_apply, hprod, hRQ, hRK]
  have hRₑ (k : Fin n) :
    Rₑ[i][k] = ℛ ((θ[k] - θ[i])) := by
    simpa [Rₑ, R, instGetElemFinNat] using (rel_linear rfl h hzero i k).symm
  have hscore (k : Fin n) :
    S i k = Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ) := by
    rw [hentry k]
    change ℛ θ[i] *ᵥ Q[i] ⬝ᵥ ℛ θ[k] *ᵥ K[k] / √(d + d : ℝ) =
      Q[i] ⬝ᵥ Rₑ[i][k] *ᵥ K[k] / √(d + d : ℝ)
    rw [hdot θ[i] θ[k] Q[i] K[k], ← hRₑ k]
  rw [Matrix.mul_apply]
  simp_rw [hsm, ← hscore]
  have hden :
    (∑ k : Fin n,
        (R[i] *ᵥ Q[i] ⬝ᵥ R[k] *ᵥ K[k] / √(d + d : ℝ)).exp) =
      ∑ k : Fin n, (S i k).exp := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hentry k]
  rw [hden]
  let D : ℝ := ∑ k : Fin n, (S i k).exp
  have hdiv :
    (∑ k : Fin n, (S i k).exp / D * V[k][j]) =
      (∑ k : Fin n, V[k][j] * (S i k).exp) / D := by
    have hterm (k : Fin n) :
      (S i k).exp / D * V[k][j] = V[k][j] * (S i k).exp / D := by
      rw [div_mul_eq_mul_div, mul_comm]
    simp_rw [hterm]
    exact (Finset.sum_div Finset.univ (fun k => V[k][j] * (S i k).exp) D).symm
  simpa [D, Matrix.mul_apply] using hdiv


-- created on 2026-11-21
