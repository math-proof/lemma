import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Def.Topology.Algebra.InfiniteSum.RiemannRearrangement.Part2


namespace Series.RiemannRearrangementWanted

open BigOperators

/-- Infinitely many nonnegative terms; otherwise the positive part would be summable. -/
theorem posSet_infinite (f : ℕ → ℝ) (s : ℝ) (hf : OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) :
    (Set.ofPred fun n => 0 ≤ f n).Infinite := by
  have hpos : ¬ Summable (fun n => max (f n) 0) := not_summable_pos_of f s hf hfa
  by_contra hfin
  rw [Set.not_infinite] at hfin
  apply hpos
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  by_contra hlt
  push Not at hlt
  apply hn
  change max (f n) 0 = 0
  rw [max_eq_right (le_of_lt hlt)]

/-- Infinitely many negative terms; otherwise the negative part would be summable. -/
theorem negSet_infinite (f : ℕ → ℝ) (s : ℝ) (hf : OrderedHasSum f s)
    (hfa : ¬ Summable (fun n => |f n|)) :
    (Set.ofPred fun n => f n < 0).Infinite := by
  have hneg : ¬ Summable (fun n => max (-f n) 0) := not_summable_neg_of f s hf hfa
  by_contra hfin
  rw [Set.not_infinite] at hfin
  apply hneg
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  by_contra hlt
  push Not at hlt
  apply hn
  change max (-f n) 0 = 0
  rw [max_eq_right (neg_nonpos.mpr hlt)]

/-- The enumerated nonnegative terms still diverge to `+∞`: their partial sums form a
subsequence of the positive-part partial sums. -/
theorem enum_pos_diverge (f : ℕ → ℝ)
    (htop : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, max (f n) 0)
      Filter.atTop Filter.atTop)
    (hP : (Set.ofPred fun n => 0 ≤ f n).Infinite) :
    Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, f (posEnum f i))
      Filter.atTop Filter.atTop := by
  have hp : StrictMono (posEnum f) := Nat.nth_strictMono hP
  have hmem : ∀ i : ℕ, 0 ≤ f (posEnum f i) :=
    fun i => Nat.nth_mem_of_infinite hP i
  have hnth : ∀ n : ℕ, 0 ≤ f n →
      Nat.nth (fun n => 0 ≤ f n) (Nat.count (fun n => 0 ≤ f n) n) = n :=
    fun n hn => Nat.nth_count hn
  have key : ∀ N : ℕ, (∑ i ∈ Finset.range N, f (posEnum f i))
      = ∑ n ∈ Finset.range (posEnum f N), max (f n) 0 := by
    intro N
    have hsub : (Finset.range (posEnum f N)).filter (fun n => 0 ≤ f n)
        ⊆ Finset.range (posEnum f N) :=
      Finset.filter_subset _ _
    have hzero : ∀ x ∈ Finset.range (posEnum f N),
        x ∉ (Finset.range (posEnum f N)).filter (fun n => 0 ≤ f n) →
        max (f x) 0 = 0 := by
      intro x hxmem hx
      have hle : ¬ 0 ≤ f x := by
        simp only [Finset.mem_filter, not_and] at hx
        exact hx hxmem
      rw [max_eq_right (le_of_lt (lt_of_not_ge hle))]
    have heq : (Finset.range (posEnum f N)).filter (fun n => 0 ≤ f n)
        = (Finset.range N).image (posEnum f) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hn, hPn⟩
        have hlt : Nat.count (fun n => 0 ≤ f n) n < N := by
          by_contra hcon
          push Not at hcon
          have h1 := hp.monotone hcon
          have h2 : posEnum f (Nat.count (fun n => 0 ≤ f n) n) = n := hnth n hPn
          omega
        refine ⟨Nat.count (fun n => 0 ≤ f n) n, hlt, ?_⟩
        show posEnum f _ = n
        simp only [posEnum]
        exact hnth n hPn
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hp hi, hmem i⟩
    calc (∑ i ∈ Finset.range N, f (posEnum f i))
        = ∑ i ∈ Finset.range N, max (f (posEnum f i)) 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [max_eq_left (hmem i)]
      _ = ∑ n ∈ (Finset.range N).image (posEnum f), max (f n) 0 := by
          rw [Finset.sum_image (fun x _ y _ hxy => hp.injective hxy)]
      _ = ∑ n ∈ Finset.range (posEnum f N), max (f n) 0 := by
          rw [← heq]
          exact Finset.sum_subset hsub hzero
  have hcomp : (fun N => ∑ i ∈ Finset.range N, f (posEnum f i))
      = (fun N => ∑ n ∈ Finset.range N, max (f n) 0) ∘ posEnum f :=
    funext key
  rw [hcomp]
  exact htop.comp hp.tendsto_atTop

/-- The enumerated negative terms (negated) still diverge to `+∞`. -/
theorem enum_neg_diverge (f : ℕ → ℝ)
    (htop : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, max (-f n) 0)
      Filter.atTop Filter.atTop)
    (hQ : (Set.ofPred fun n => f n < 0).Infinite) :
    Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, -f (negEnum f j))
      Filter.atTop Filter.atTop := by
  have hq : StrictMono (negEnum f) := Nat.nth_strictMono hQ
  have hmem : ∀ j : ℕ, 0 ≤ -f (negEnum f j) :=
    fun j => le_of_lt (neg_pos.mpr (Nat.nth_mem_of_infinite hQ j))
  have hmemQ : ∀ j : ℕ, f (negEnum f j) < 0 :=
    fun j => Nat.nth_mem_of_infinite hQ j
  have hnth : ∀ n : ℕ, f n < 0 →
      Nat.nth (fun n => f n < 0) (Nat.count (fun n => f n < 0) n) = n :=
    fun n hn => Nat.nth_count hn
  have key : ∀ N : ℕ, (∑ j ∈ Finset.range N, -f (negEnum f j))
      = ∑ n ∈ Finset.range (negEnum f N), max (-f n) 0 := by
    intro N
    have hsub : (Finset.range (negEnum f N)).filter (fun n => f n < 0)
        ⊆ Finset.range (negEnum f N) :=
      Finset.filter_subset _ _
    have hzero : ∀ x ∈ Finset.range (negEnum f N),
        x ∉ (Finset.range (negEnum f N)).filter (fun n => f n < 0) →
        max (-f x) 0 = 0 := by
      intro x hxmem hx
      have hle : ¬ f x < 0 := by
        simp only [Finset.mem_filter, not_and] at hx
        exact hx hxmem
      rw [max_eq_right (neg_nonpos.mpr (not_lt.mp hle))]
    have heq : (Finset.range (negEnum f N)).filter (fun n => f n < 0)
        = (Finset.range N).image (negEnum f) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hn, hQn⟩
        have hlt : Nat.count (fun n => f n < 0) n < N := by
          by_contra hcon
          push Not at hcon
          have h1 := hq.monotone hcon
          have h2 : negEnum f (Nat.count (fun n => f n < 0) n) = n := hnth n hQn
          omega
        refine ⟨Nat.count (fun n => f n < 0) n, hlt, ?_⟩
        show negEnum f _ = n
        simp only [negEnum]
        exact hnth n hQn
      · rintro ⟨j, hj, rfl⟩
        exact ⟨hq hj, hmemQ j⟩
    calc (∑ j ∈ Finset.range N, -f (negEnum f j))
        = ∑ j ∈ Finset.range N, max (-f (negEnum f j)) 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [max_eq_left (hmem j)]
      _ = ∑ n ∈ (Finset.range N).image (negEnum f), max (-f n) 0 := by
          rw [Finset.sum_image (fun x _ y _ hxy => hq.injective hxy)]
      _ = ∑ n ∈ Finset.range (negEnum f N), max (-f n) 0 := by
          rw [← heq]
          exact Finset.sum_subset hsub hzero
  have hcomp : (fun N => ∑ j ∈ Finset.range N, -f (negEnum f j))
      = (fun N => ∑ n ∈ Finset.range N, max (-f n) 0) ∘ negEnum f :=
    funext key
  rw [hcomp]
  exact htop.comp hq.tendsto_atTop

end Series.RiemannRearrangementWanted
