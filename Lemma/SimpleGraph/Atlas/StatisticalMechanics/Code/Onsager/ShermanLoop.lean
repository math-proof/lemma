import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
open StatMech StatMech.Onsager


/--
[ons_loopWeight_cyclicShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLoop.lean)
-/
@[path]
private lemma ons_loopWeight_cyclicShift_eq
  {E}
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E} :
-- imply
  ons_loopWeight Λ (ons_cyclicShift v) = ons_loopWeight Λ v := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_cyclicShift Λ v

/--
[ons_trace_pow_eq_loopWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLoop.lean)
-/
@[path]
private lemma ons_trace_pow_eq_loopWeight_sum_eq
  {E}
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
-- given
  (hn : 0 < n) :
-- imply
  (Λ ^ n).trace = ∑ v : Fin n → E, ons_loopWeight Λ v := by
-- proof
  apply StatMech.Onsager.ons_trace_pow_eq_loopWeight_sum Λ n hn

/--
[ons_loopWeight_cyclicShift_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLoop.lean)
-/
@[path]
private lemma ons_loopWeight_cyclicShift_iterate_eq
  {E}
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
  {v : Fin n → E}
  {j : ℕ} :
-- imply
  ons_loopWeight Λ (ons_cyclicShift^[j] v) = ons_loopWeight Λ v := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_cyclicShift_iterate Λ v j


-- created on 2026-10-23
