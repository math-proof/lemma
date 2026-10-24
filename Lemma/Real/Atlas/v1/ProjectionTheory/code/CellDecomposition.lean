import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.CellDecomposition
open Finset Set MvPolynomial CellDecomposition
open Classical


namespace CellDecomposition

/--
[polyCell_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma polyCell_isOpen
  {k : ℕ}
  {polys : Fin k → MvPolynomial (Fin 2) ℝ}
  {σ : Fin k → Bool} :
-- imply
  IsOpen (polyCell polys σ) := by
-- proof
  apply isOpen_iInter_of_finite; intro i
  split_ifs
  · exact isOpen_lt continuous_const (continuous_eval _)
  · exact isOpen_lt (continuous_eval _) continuous_const

end CellDecomposition

namespace CellDecomposition

/--
[polyWall_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma polyWall_isClosed
  {k : ℕ}
  {polys : Fin k → MvPolynomial (Fin 2) ℝ} :
-- imply
  IsClosed (polyWall polys) := by
-- proof
  apply isClosed_iUnion_of_finite; intro i
  exact isClosed_eq (continuous_eval _) continuous_const

end CellDecomposition

namespace CellDecomposition

/--
[polyWall_union_cells](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma polyWall_union_cells
  {k : ℕ}
  {polys : Fin k → MvPolynomial (Fin 2) ℝ} :
-- imply
  polyWall polys ∪ ⋃ σ : Fin k → Bool, polyCell polys σ = univ := by
-- proof
  ext x; simp only [mem_union, mem_iUnion, mem_univ, iff_true]
  by_cases h : ∃ i, eval x (polys i) = 0
  · left; exact mem_iUnion.mpr (h.imp fun i hi => hi)
  · right; push_neg at h
    refine ⟨fun i => decide (eval x (polys i) > 0), ?_⟩
    simp only [polyCell, mem_iInter, decide_eq_true_eq]
    intro i; have hi := h i
    split_ifs with hpos
    · exact hpos
    · push_neg at hpos; exact lt_of_le_of_ne hpos hi

end CellDecomposition

namespace CellDecomposition

/--
[polyCell_pairwise_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma polyCell_pairwise_disjoint
  {k : ℕ}
  {polys : Fin k → MvPolynomial (Fin 2) ℝ} :
-- imply
  Pairwise fun σ τ : Fin k → Bool => Disjoint (polyCell polys σ) (polyCell polys τ) := by
-- proof
  intro σ τ hne; rw [Set.disjoint_left]
  intro x hx hτ
  simp only [polyCell, mem_iInter] at hx hτ
  apply hne; funext i
  have hxi := hx i; have hτi := hτ i
  cases hσ : σ i <;> cases hτ' : τ i <;> simp_all <;> linarith

end CellDecomposition

namespace CellDecomposition

/--
[polyCell_disjoint_wall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma polyCell_disjoint_wall
  {k : ℕ}
  {polys : Fin k → MvPolynomial (Fin 2) ℝ}
  {σ : Fin k → Bool} :
-- imply
  Disjoint (polyCell polys σ) (polyWall polys) := by
-- proof
  rw [Set.disjoint_left]; intro x hx hw
  simp only [polyCell, mem_iInter] at hx
  simp only [polyWall, mem_iUnion] at hw
  obtain ⟨i, hi⟩ := hw
  have hxi := hx i
  cases hσi : σ i <;> simp_all <;> linarith

end CellDecomposition

namespace CellDecomposition

/--
[signPatternCell_snoc_true_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma signPatternCell_snoc_true_subset
  {X : Finset (Fin 2 → ℝ)}
  {k : ℕ}
  {polys : Fin k → MvPolynomial (Fin 2) ℝ}
  {p : MvPolynomial (Fin 2) ℝ}
  {σ : Fin k → Bool} :
-- imply
  signPatternCell X (Fin.snoc polys p) (Fin.snoc σ true) ⊆ (signPatternCell X polys σ).filter (fun x => eval x p > 0) := by
-- proof
  intro x hx; simp only [signPatternCell, Finset.mem_filter] at hx ⊢
  refine ⟨⟨hx.1, fun i => ?_⟩, ?_⟩
  · have := hx.2 (Fin.castSucc i); simp [Fin.snoc_castSucc] at this; exact this
  · have := hx.2 (Fin.last k); simp [Fin.snoc_last] at this; exact this

end CellDecomposition

namespace CellDecomposition

/--
[signPatternCell_snoc_false_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma signPatternCell_snoc_false_subset
  {X : Finset (Fin 2 → ℝ)}
  {k : ℕ}
  {polys : Fin k → MvPolynomial (Fin 2) ℝ}
  {p : MvPolynomial (Fin 2) ℝ}
  {σ : Fin k → Bool} :
-- imply
  signPatternCell X (Fin.snoc polys p) (Fin.snoc σ false) ⊆ (signPatternCell X polys σ).filter (fun x => eval x p < 0) := by
-- proof
  intro x hx; simp only [signPatternCell, Finset.mem_filter] at hx ⊢
  refine ⟨⟨hx.1, fun i => ?_⟩, ?_⟩
  · have := hx.2 (Fin.castSucc i); simp [Fin.snoc_castSucc] at this; exact this
  · have := hx.2 (Fin.last k); simp [Fin.snoc_last] at this; exact this

end CellDecomposition

namespace CellDecomposition

/--
[degree_bound_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma degree_bound_step
  {j : ℕ} :
-- imply
  2 ^ j ≤ (2 ^ ((j + 1) / 2)) ^ 2 := by
-- proof
  have h : j ≤ 2 * ((j + 1) / 2) := by omega
  calc 2 ^ j ≤ 2 ^ (2 * ((j + 1) / 2)) := Nat.pow_le_pow_right (by norm_num) h
    _ = (2 ^ ((j + 1) / 2)) ^ 2 := by ring

end CellDecomposition

namespace CellDecomposition

/--
[card_fin_bool_fun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma card_fin_bool_fun
  {k : ℕ} :
-- imply
  Fintype.card (Fin k → Bool) = 2 ^ k := by
-- proof
  simp [Fintype.card_fin, Fintype.card_bool]

end CellDecomposition

namespace CellDecomposition

/--
[degree_sum_bound_even](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma degree_sum_bound_even
  {m : ℕ} :
-- imply
  ∑ j ∈ Finset.range (2 * m), 2 ^ ((j + 1) / 2) = 3 * (2 ^ m - 1) := by
-- proof
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h2 : (2 * m + 0 + 1) / 2 = m := by omega
    rw [h1, h2]; ring_nf; omega

end CellDecomposition

namespace CellDecomposition

/--
[degree_sum_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma degree_sum_bound
  {k : ℕ} :
-- imply
  ∑ j ∈ Finset.range k, 2 ^ ((j + 1) / 2) ≤ 4 * 2 ^ (k / 2) := by
-- proof
  obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Nat.even_or_odd k
  · have hk : k = 2 * m := by omega
    rw [hk, degree_sum_bound_even]
    have h : 2 * m / 2 = m := by omega
    rw [h]; omega
  · have hk : k = 2 * m + 1 := by omega
    rw [hk, show 2 * m + 1 = (2 * m) + 1 from by ring,
      Finset.sum_range_succ, degree_sum_bound_even]
    have h1 : (2 * m + 0 + 1) / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1]; omega

end CellDecomposition

namespace CellDecomposition

/--
[two_pow_log_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma two_pow_log_bound
  {s : ℕ}
-- given
  (hs : 1 ≤ s) :
-- imply
  s ^ 2 ≤ 2 ^ (2 * Nat.log 2 s + 2) := by
-- proof
  have h1 : s ≤ 2 ^ (Nat.log 2 s + 1) := (Nat.lt_pow_succ_log_self (by norm_num) s).le
  calc s ^ 2 ≤ (2 ^ (Nat.log 2 s + 1)) ^ 2 := Nat.pow_le_pow_left h1 _
    _ = 2 ^ (2 * Nat.log 2 s + 2) := by ring

end CellDecomposition

namespace CellDecomposition

/--
[two_pow_half_log_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean)
-/
@[path]
lemma two_pow_half_log_bound
  {s : ℕ}
-- given
  (hs : 1 ≤ s) :
-- imply
  2 ^ ((2 * Nat.log 2 s + 2) / 2) ≤ 2 * s := by
-- proof
  have h : (2 * Nat.log 2 s + 2) / 2 = Nat.log 2 s + 1 := by omega
  rw [h]
  have : 2 ^ Nat.log 2 s ≤ s := Nat.pow_log_le_self 2 (by omega : s ≠ 0)
  calc 2 ^ (Nat.log 2 s + 1) = 2 * 2 ^ Nat.log 2 s := by ring
    _ ≤ 2 * s := by linarith
/--
Iterated polynomial ham-sandwich bisection. For any finite `X ⊆ ℝ²` and any
`k`, there exist polynomials `polys₀, …, polys_{k−1}` (all nonzero) with
`deg(polys i) ≤ 2^{⌊(i+1)/2⌋}` such that each of the `2^k` sign-pattern cells
contains at most `|X| / 2^k` points of `X`.
-/
section
open Classical
end

end CellDecomposition


-- created on 2026-10-23
