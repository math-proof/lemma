import Mathlib
import sympy.Basic
import sympy.series.RiemannRearrangement

open Series.RiemannRearrangementWanted

/--
[RiemannRearrangement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/RiemannRearrangement.lean)
-/
@[path]
private lemma ordered_has_sum_iff
-- given
  (f : ℕ → ℝ)
  (a : ℝ) :
-- imply
  OrderedHasSum f a ↔
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds a) := by
-- proof
  apply Series.RiemannRearrangementWanted.orderedHasSum_iff f a

/--
[RiemannRearrangement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/RiemannRearrangement.lean)
-/
@[path]
private lemma ordered_has_sum_tendsto_zero_is
-- given
  (f : ℕ → ℝ)
  (s : ℝ)
  (h : OrderedHasSum f s) :
-- imply
  Filter.Tendsto f Filter.atTop (nhds 0) := by
-- proof
  apply Series.RiemannRearrangementWanted.orderedHasSum_tendsto_zero f s h

/--
[RiemannRearrangement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Series/RiemannRearrangement.lean)
-/
@[path]
private lemma riemann_rearrangement_is
-- given
  (f : ℕ → ℝ)
  (hf : ∃ s, OrderedHasSum f s)
  (hfa : ¬ Summable fun n => |f n|)
  (a : ℝ) :
-- imply
  ∃ e : Equiv.Perm ℕ, OrderedHasSum (fun n => f (e n)) a := by
-- proof
  apply Series.RiemannRearrangementWanted.riemann_rearrangement f hf hfa a

-- created on 2026-10-10
