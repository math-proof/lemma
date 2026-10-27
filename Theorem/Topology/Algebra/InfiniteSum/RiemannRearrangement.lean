import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Def.Topology.Algebra.InfiniteSum.RiemannRearrangement


namespace Series.RiemannRearrangementWanted

open BigOperators

/-- `OrderedHasSum f a` unfolds to convergence of the ordered partial sums. -/
theorem orderedHasSum_iff (f : ℕ → ℝ) (a : ℝ) :
    OrderedHasSum f a ↔
      Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds a) :=
  Iff.rfl

/-- Convergent ordered series have vanishing terms. -/
theorem orderedHasSum_tendsto_zero (f : ℕ → ℝ) (s : ℝ) (h : OrderedHasSum f s) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have hsucc' : Filter.Tendsto (fun N => N + 1) (Filter.atTop : Filter ℕ) Filter.atTop :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr Filter.tendsto_id
  have hsucc : Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), f n) Filter.atTop (nhds s) :=
    h.comp hsucc'
  have hdiff : Filter.Tendsto
      (fun N => (∑ n ∈ Finset.range (N + 1), f n) - (∑ n ∈ Finset.range N, f n))
      Filter.atTop (nhds (s - s)) := hsucc.sub h
  simp only [sub_self] at hdiff
  have heq : (fun N => (∑ n ∈ Finset.range (N + 1), f n) - (∑ n ∈ Finset.range N, f n)) = f := by
    funext N
    rw [Finset.sum_range_succ]
    ring
  rwa [heq] at hdiff

theorem max_neg_eq (x : ℝ) : max (-x) 0 = max x 0 - x := by
  by_cases h : 0 ≤ x
  · simp [max_eq_left h, max_eq_right (by linarith : -x ≤ 0)]
  · push Not at h
    simp [max_eq_right (le_of_lt (by linarith : x < 0)), max_eq_left (by linarith : 0 ≤ -x)]

theorem abs_eq_max_add (x : ℝ) : |x| = max x 0 + max (-x) 0 := by
  by_cases h : 0 ≤ x
  · simp [max_eq_left h, max_eq_right (by linarith : -x ≤ 0), abs_of_nonneg h]
  · push Not at h
    simp [max_eq_right (le_of_lt (by linarith : x < 0)), max_eq_left (by linarith : 0 ≤ -x),
      abs_of_neg (by linarith : x < 0)]

/-- Positive part diverges for a conditionally convergent series. -/
theorem not_summable_pos_of (f : ℕ → ℝ) (s : ℝ) (hf : OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) :
    ¬ Summable (fun n => max (f n) 0) := by
  intro hpos
  have hpos_sum : OrderedHasSum (fun n => max (f n) 0) (∑' n, max (f n) 0) :=
    (hpos.hasSum).tendsto_sum_nat
  have hneg_eq : (fun n => max (-f n) 0) = (fun n => max (f n) 0 - f n) := by
    funext n
    exact max_neg_eq (f n)
  have hneg_sum : OrderedHasSum (fun n => max (-f n) 0) ((∑' n, max (f n) 0) - s) := by
    rw [hneg_eq]
    have hsub : Filter.Tendsto
        (fun N => (∑ n ∈ Finset.range N, max (f n) 0) - (∑ n ∈ Finset.range N, f n))
        Filter.atTop (nhds ((∑' n, max (f n) 0) - s)) := hpos_sum.sub hf
    have heq : (fun N => (∑ n ∈ Finset.range N, (max (f n) 0 - f n)))
        = (fun N => (∑ n ∈ Finset.range N, max (f n) 0) - (∑ n ∈ Finset.range N, f n)) := by
      funext N
      rw [Finset.sum_sub_distrib]
    change Filter.Tendsto _ _ _
    rw [heq]
    exact hsub
  have habs_eq : (fun n => |f n|) = (fun n => max (f n) 0 + max (-f n) 0) := by
    funext n
    exact abs_eq_max_add (f n)
  have hnonneg_abs : ∀ n : ℕ, 0 ≤ |f n| := fun n => abs_nonneg _
  have habs_sum :
      OrderedHasSum (fun n => |f n|) ((∑' n, max (f n) 0) + ((∑' n, max (f n) 0) - s)) := by
    rw [habs_eq]
    have hadd : Filter.Tendsto
        (fun N => (∑ n ∈ Finset.range N, max (f n) 0) + (∑ n ∈ Finset.range N, max (-f n) 0))
        Filter.atTop (nhds ((∑' n, max (f n) 0) + ((∑' n, max (f n) 0) - s))) :=
      hpos_sum.add hneg_sum
    have heq : (fun N => (∑ n ∈ Finset.range N, (max (f n) 0 + max (-f n) 0)))
        = (fun N => (∑ n ∈ Finset.range N, max (f n) 0) +
            (∑ n ∈ Finset.range N, max (-f n) 0)) := by
      funext N
      rw [Finset.sum_add_distrib]
    change Filter.Tendsto _ _ _
    rw [heq]
    exact hadd
  have habs_summable : Summable (fun n => |f n|) :=
    ((hasSum_iff_tendsto_nat_of_nonneg hnonneg_abs _).mpr habs_sum).summable
  exact hfa habs_summable

/-- Negative part diverges for a conditionally convergent series. -/
theorem not_summable_neg_of (f : ℕ → ℝ) (s : ℝ) (hf : OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) :
    ¬ Summable (fun n => max (-f n) 0) := by
  have hneg_ordered : OrderedHasSum (fun n => -f n) (-s) := by
    have h : Filter.Tendsto (fun N => -(∑ n ∈ Finset.range N, f n)) Filter.atTop (nhds (-s)) :=
      hf.neg
    have heq : (fun N => ∑ n ∈ Finset.range N, (-f n))
        = (fun N => -(∑ n ∈ Finset.range N, f n)) := by
      funext N
      rw [Finset.sum_neg_distrib]
    change Filter.Tendsto _ _ _
    rw [heq]
    exact h
  have habs_eq : (fun n => |(-f n)|) = (fun n => |f n|) := by
    funext n
    rw [abs_neg]
  have hfa' : ¬ Summable (fun n => |(-f n)|) := by
    rwa [habs_eq]
  have h := not_summable_pos_of (fun n => -f n) (-s) hneg_ordered hfa'
  simpa using h

end Series.RiemannRearrangementWanted
