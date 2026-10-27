import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.KyFan
open InnerProductSpace.KyFanWanted


/--
[KyFan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/KyFan.lean)
-/
@[path]
private lemma eig_pref_sum_succ_eq
-- given
  {n : ℕ}
  (k : ℕ)
  (hk : k + 1 ≤ n)
  (eig : Fin n → ℝ) :
-- imply
  eigPrefSum eig (k + 1) hk = eigPrefSum eig k (Nat.le_of_succ_le hk) + eig ⟨k, hk⟩ := by
-- proof
  apply InnerProductSpace.KyFanWanted.eigPrefSum_succ eig k hk


-- created on 2026-10-24
