import Mathlib.Analysis.SpecialFunctions.Exp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open scoped BigOperators


/-!
# Complete exponential autonomous functions

Source: José Luis López, *Exponential Autonomous Functions*:
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Orozco/orozco5.tex>.
-/

namespace MetaMathlibExt

/-- Complete Bell polynomial family `B n`, as used in source statement
`jis_4e6064ed86b521df4a4febe5` (concept `jis_sem_2f450d618ad4cc4cadb7505f`).

`B 0` is `1`, and `B (m + 1)` applied to `x : Nat → Complex` (with `x i`
standing for `y_{i+1}`) is
`∑ i ∈ Finset.range (m + 1), C(m, i) * B (m - i) x * x i`. -/
noncomputable def completeBellPolynomial (n : Nat) (x : Nat → Complex) : Complex :=
  Nat.strongRecOn (motive := fun _ => (Nat → Complex) → Complex) n
    (fun m ih x =>
      match m with
      | 0 => 1
      | m + 1 =>
        ∑ i ∈ Finset.range (m + 1),
          (m.choose i : Complex) * ih (m - i) (by omega) x * x i) x

@[simp]
theorem completeBellPolynomial_zero (x : ℕ → ℂ) : completeBellPolynomial 0 x = 1 := by
  rw [completeBellPolynomial, Nat.strongRecOn_eq]

@[simp]
theorem completeBellPolynomial_one (x : ℕ → ℂ) : completeBellPolynomial 1 x = x 0 := by
  rw [completeBellPolynomial, Nat.strongRecOn_eq]
  simp [Nat.strongRecOn_eq]

@[simp]
theorem completeBellPolynomial_two (x : ℕ → ℂ) :
    completeBellPolynomial 2 x = x 0 ^ 2 + x 1 := by
  rw [completeBellPolynomial, Nat.strongRecOn_eq]
  norm_num [Finset.sum_range_succ, pow_two]
  rw [Nat.strongRecOn_eq, Nat.strongRecOn_eq]
  ring_nf
  rw [Nat.strongRecOn_eq]
  simp only [one_mul]

/-- N-th complete exponential autonomous function of order `k` (`k ≥ 1`), with
parameter `a : Complex` and variables `x = (x₁, …, xₖ)`, as specified in source
statement `jis_4e6064ed86b521df4a4febe5` (concept `jis_sem_2f450d618ad4cc4cadb7505f`).

Initial values: `f 0 = x 0` through `f (k - 1) = x (k - 1)`, `f k = a * exp (x 0)`.
Recurrence: for `n > k`, with `m = n - k ≥ 1`,
`f n = a * exp (x 0) * B m (f 1, …, f m)`, where `B` is the complete Bell
polynomial family `completeBellPolynomial` (argument `i : Nat` standing for
`f (i + 1)`). -/
noncomputable def completeExponentialAutonomousFunction (k : Nat) (hk : 0 < k)
    (a : Complex) (x : Fin k → Complex) : Nat → Complex :=
  fun N =>
    Nat.strongRecOn (motive := fun _ => Complex) N (fun n ih =>
      if h : n < k then x ⟨n, h⟩
      else if _h2 : n = k then a * Complex.exp (x ⟨0, hk⟩)
      else
        a * Complex.exp (x ⟨0, hk⟩) *
          completeBellPolynomial (n - k) (fun i =>
            if h3 : i + 1 < n then ih (i + 1) h3 else 0))

end MetaMathlibExt
