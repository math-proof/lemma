import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.KyFan
open InnerProductSpace.KyFanWanted


/--
[KyFan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/KyFan.lean)
-/
@[path]
private lemma eig_pref_sum_zero_eq
-- given
  {n : ℕ}
  (hk : 0 ≤ n)
  (eig : Fin n → ℝ) :
-- imply
  eigPrefSum eig 0 hk = 0 := by
-- proof
  apply InnerProductSpace.KyFanWanted.eigPrefSum_zero eig hk


-- created on 2026-10-24
