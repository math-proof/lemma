import Mathlib
import sympy.Basic
import Instance.v1.Atlas.Buildings.code.Valuation.DVRInstances
open DVRContext


/--
[perm_exists_gt_of_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean)
-/
@[path]
private lemma perm_exists_gt_of_ne_one_eq
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {m : ℕ}
  {σ : Equiv.Perm (Fin m)}
-- given
  (hσ : σ ≠ 1) :
-- imply
  ∃ i : Fin m, i < σ i := by
-- proof
  apply perm_exists_gt_of_ne_one p σ hσ


-- created on 2026-10-24
