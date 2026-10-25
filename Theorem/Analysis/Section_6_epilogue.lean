import Mathlib
import Theorem.Analysis.Section_6_7.Part2
open Filter

/-!
# Analysis I, Chapter 6 epilogue: Connections with Mathlib limits

In this (technical) epilogue, we show that various operations and properties we have defined for
"Chapter 6" sequences {name}`Chapter6.Sequence` are equivalent to Mathlib operations.  Note however
that Mathlib's operations are defined in far greater generality than the setting of real-valued
sequences, in particular using the language of filters.

-/


/-- Identification with the Cauchy sequence support in Mathlib/Algebra/Order/CauSeq/Basic -/
theorem Chapter6.Sequence.isCauchy_iff_isCauSeq (a: ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ IsCauSeq _root_.abs a := by
  simp_rw [IsCauchy.coe, Real.dist_eq, IsCauSeq]
  constructor <;> intro h ε hε <;> have ⟨ N, h ⟩ := h _ (half_pos hε) <;> use N
  . intro n hn; linarith [h n hn N (by rfl)]
  intro n hn m hm
  calc
    _ ≤ |a n - a N| + |a m - a N| := by grind [abs_sub_comm, abs_sub_le]
    _ ≤ ε/2 + ε/2 := by grind
    _ = _ := by linarith

/-- Identification with the Cauchy sequence support in Mathlib/Topology/UniformSpace/Cauchy -/
theorem Chapter6.Sequence.Cauchy_iff_CauchySeq (a: ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ CauchySeq a := by
  rw [isCauchy_iff_isCauSeq]
  convert isCauSeq_iff_cauchySeq

/-- Identification with {name}`Filter.Tendsto` -/
theorem Chapter6.Sequence.tendsto_iff_Tendsto (a: ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ atTop.Tendsto a (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor <;> intro h ε hε
  . have ⟨ N, hN ⟩ := h _ (half_pos hε); use N.toNat; intro n hn
    specialize hN n (Int.toNat_le.mp hn); simp at hN
    rw [Real.dist_eq]; linarith
  have ⟨ N, hN ⟩ := h ε hε; use N; intro n hn
  have hpos : n ≥ 0 := by grind
  rw [ge_iff_le, ←Int.le_toNat hpos] at hn
  simp [hpos, ←Real.dist_eq, le_of_lt (hN n.toNat hn)]

theorem Chapter6.Sequence.tendsto_iff_Tendsto' (a: Sequence) (L:ℝ) : a.TendsTo L ↔ atTop.Tendsto a.seq (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor <;> intro h ε hε
  . have ⟨ N, hN ⟩ := h _ (half_pos hε); use N; peel 2 hN; rw [Real.dist_eq]; linarith
  have ⟨ N, hN ⟩ := h _ hε; use N; peel 2 hN; rw [←Real.dist_eq]; linarith

theorem Chapter6.Sequence.converges_iff_Tendsto (a: ℕ → ℝ) :
    (a:Sequence).Convergent ↔ ∃ L, atTop.Tendsto a (nhds L) := by simp_rw [←tendsto_iff_Tendsto]

theorem Chapter6.Sequence.converges_iff_Tendsto' (a: Sequence) :
    a.Convergent ↔ ∃ L, atTop.Tendsto a.seq (nhds L) := by simp_rw [←tendsto_iff_Tendsto']

