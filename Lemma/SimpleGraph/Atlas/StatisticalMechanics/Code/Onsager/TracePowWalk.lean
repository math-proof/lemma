import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
open StatMech StatMech.Onsager


/--
[ons_pow_apply_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TracePowWalk.lean)
-/
@[path]
private lemma ons_pow_apply_walk_eq
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ} :
-- imply
  ∀ (n : ℕ) (i j : E), (Λ ^ n) i j = ∑ p : Fin n → E, (if (Fin.cons i p : Fin (n + 1) → E) (Fin.last n) = j then (1 : ℂ) else 0) * ∏ k : Fin n, Λ ((Fin.cons i p : Fin (n + 1) → E) k.castSucc) (p k) := by
-- proof
  apply StatMech.Onsager.ons_pow_apply_walk Λ

/--
[ons_trace_pow_eq_walk_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TracePowWalk.lean)
-/
@[path]
private lemma ons_trace_pow_eq_walk_sum_eq
  [Fintype E]
  [DecidableEq E]
  {Λ : Matrix E E ℂ}
  {n : ℕ}
  [NeZero n]
-- given
  (hn : 0 < n) :
-- imply
  (Λ ^ n).trace = ∑ v : Fin n → E, ∏ k : Fin n, Λ (v k) (v (k + 1)) := by
-- proof
  apply StatMech.Onsager.ons_trace_pow_eq_walk_sum Λ n hn


-- created on 2026-10-23
