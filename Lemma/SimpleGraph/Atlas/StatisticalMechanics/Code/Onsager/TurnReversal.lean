import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TurnReversal
open StatMech StatMech.Onsager


/--
[ons_turnPow_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurnReversal.lean)
-/
@[path]
private lemma ons_turnPow_rev_eq
  {μ ν : Fin 4} :
-- imply
  ons_turnPow (ν + 2) (μ + 2) = - ons_turnPow μ ν := by
-- proof
  apply StatMech.Onsager.ons_turnPow_rev μ ν

/--
[ons_turnW_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurnReversal.lean)
-/
@[path]
private lemma ons_turnW_rev_eq
  {ω : ℂ}
  {μ ν : Fin 4} :
-- imply
  ons_turnW ω (ν + 2) (μ + 2) = (ons_turnW ω μ ν)⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_turnW_rev ω μ ν

/--
[ons_turnPow_sum_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurnReversal.lean)
-/
@[path]
private lemma ons_turnPow_sum_rev_eq
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4} :
-- imply
  (∑ k : Fin n, ons_turnPow ((fun j => d (Fin.rev j) + 2) k.castSucc) ((fun j => d (Fin.rev j) + 2) k.succ)) = - ∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) := by
-- proof
  apply StatMech.Onsager.ons_turnPow_sum_rev n d


-- created on 2026-10-23
