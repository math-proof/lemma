import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Topology.Algebra.InfiniteSum.HardyInequality

/--
[HardyInequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/HardyInequality.lean)
-/
@[path]
private lemma hardy_inequality_le
-- given
  (a : ℕ → ℝ)
  (p : ℝ)
  (hp : 1 < p)
  (hnonneg : ∀ n, 0 ≤ a n)
  (hsumm : Summable fun n => (a n).rpow p) :
-- imply
  Summable (fun n => ((Finset.sum (Finset.range (n + 1)) a / ((n : ℝ) + 1)).rpow p)) ∧
    ∑' n, ((Finset.sum (Finset.range (n + 1)) a / ((n : ℝ) + 1)).rpow p) ≤
      (p / (p - 1)).rpow p * ∑' n, (a n).rpow p := by
-- proof
  apply MetaMathlibExt.hardy_inequality hp hnonneg hsumm

-- created on 2026-10-10
