module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.CompleteExponentialAutonomousFunction
open scoped BigOperators

/-!
# Complete exponential autonomous functions

Source: José Luis López, *Exponential Autonomous Functions*:
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Orozco/orozco5.tex>.
-/

public section


namespace MetaMathlibExt

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

end MetaMathlibExt
