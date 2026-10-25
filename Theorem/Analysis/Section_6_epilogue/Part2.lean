import Mathlib
import Theorem.Analysis.Section_6_7.Part2
import Instance.Analysis.Section_6_epilogue
open Filter

/-!
# Analysis I, Chapter 6 epilogue: Connections with Mathlib limits

In this (technical) epilogue, we show that various operations and properties we have defined for
"Chapter 6" sequences {name}`Chapter6.Sequence` are equivalent to Mathlib operations.  Note however
that Mathlib's operations are defined in far greater generality than the setting of real-valued
sequences, in particular using the language of filters.

-/


/-- Identification with {name}`CauSeq.lim` -/
theorem Chapter6.Sequence.lim_eq_CauSeq_lim (a:ℕ → ℝ) (ha: (a:Sequence).IsCauchy) :
    Chapter6.lim (a:Sequence) = CauSeq.lim  ⟨ a, (isCauchy_iff_isCauSeq a).mp ha⟩ := by
  have h1 := CauSeq.tendsto_limit ⟨ a, (isCauchy_iff_isCauSeq a).mp ha⟩
  have h2 := lim_def ((a:Sequence).Cauchy_iff_convergent.mp ha)
  rw [←tendsto_iff_Tendsto] at h1
  by_contra! h; apply (a:Sequence).tendsTo_unique at h; tauto

/-- Identification with {name}`Bornology.IsBounded` -/
theorem Chapter6.Sequence.isBounded_iff_isBounded_range (a:ℕ → ℝ):
    (a:Sequence).IsBounded ↔ Bornology.IsBounded (Set.range a) := by
  simp [isBounded_def, boundedBy_def, Metric.isBounded_iff]
  constructor
  . intro ⟨ M, hM, h ⟩; use 2*M; intro n m
    calc
      _ = |a n - a m| := Real.dist_eq _ _
      _ ≤ |a n| + |a m| := abs_sub _ _
      _ ≤ M + M := by
        gcongr
        · simpa [Int.natCast_nonneg, Int.toNat_natCast] using h n
        · simpa [Int.natCast_nonneg, Int.toNat_natCast] using h m
      _ = _ := by ring
  intro ⟨ C, h ⟩
  have : C ≥ 0 := by specialize h 0 0; simpa using h
  refine ⟨ C + |a 0|, by positivity, ?_ ⟩
  intro n; by_cases hn: n ≥ 0 <;> simp [hn]
  . calc
      _ ≤ |a n.toNat - a 0| + |a 0| := by convert abs_add_le _ _; abel; infer_instance
      _ ≤ C + |a 0| := by gcongr; rw [←Real.dist_eq]; convert h n.toNat 0
  positivity

/-- Identification with {name}`MapClusterPt` -/
theorem Chapter6.Sequence.limit_point_iff (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ MapClusterPt L .atTop a := by
  simp_rw [limit_point_def, mapClusterPt_iff_frequently, frequently_atTop, Metric.mem_nhds_iff]
  constructor
  . intro h s ⟨ ε, hε, hεs ⟩ N
    have ⟨ n, hn1, hn2 ⟩ := h _ (half_pos hε) N (by positivity)
    have hn : n ≥ 0 := by grind
    refine ⟨ n.toNat, (Int.le_toNat hn).mpr hn1, ?_ ⟩
    apply hεs; simp [Real.dist_eq, hn] at *; linarith
  intro h ε hε N _
  have ⟨ n, hn1, hn2 ⟩ := h (Metric.ball L ε) ⟨ _, hε, by aesop ⟩ N.toNat
  have hn : n ≥ 0 := by positivity
  refine ⟨ n, by rwa [ge_iff_le, ←Int.toNat_le], ?_ ⟩
  simp [Real.dist_eq, hn] at *; linarith

