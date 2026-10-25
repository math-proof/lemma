/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Def.Combinatorics.SimpleGraph.Frucht.Part2


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

theorem fruchtShift_inl (N : ℕ) {G : Type*} [Group G] (a x : G) :
    fruchtShift N a (.inl x : G ⊕ (G × Fin N)) = .inl (a * x) := rfl

theorem fruchtShift_inr (N : ℕ) {G : Type*} [Group G] (a g : G) (j : Fin N) :
    fruchtShift N a (.inr (g, j) : G ⊕ (G × Fin N)) = .inr (a * g, j) := rfl

theorem fruchtShift_mul (N : ℕ) {G : Type*} [Group G] (a b : G) :
    fruchtShift N (a * b) = fruchtShift N a * fruchtShift N b := by
  apply Equiv.Perm.ext
  intro v
  cases v with
  | inl x =>
    change (.inl ((a * b) * x) : G ⊕ (G × Fin N)) = (fruchtShift N a * fruchtShift N b) _
    rw [Equiv.Perm.mul_apply, fruchtShift_inl, fruchtShift_inl, mul_assoc]
  | inr p =>
    obtain ⟨g, j⟩ := p
    change (.inr ((a * b) * g, j) : G ⊕ (G × Fin N)) = (fruchtShift N a * fruchtShift N b) _
    rw [Equiv.Perm.mul_apply, fruchtShift_inr, fruchtShift_inr, mul_assoc]

theorem fruchtShift_adj (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (a : G) (v w : G ⊕ (G × Fin N)) :
    (fruchtGraph N e).Adj v w ↔
      (fruchtGraph N e).Adj (fruchtShift N a v) (fruchtShift N a w) := by
  cases v with
  | inl x =>
    cases w with
    | inl y =>
      rw [fruchtShift_inl, fruchtShift_inl, fruchtGraph_adj_inl_inl,
        fruchtGraph_adj_inl_inl]
      exact (not_congr (mul_right_inj a)).symm
    | inr p =>
      obtain ⟨g, j⟩ := p
      rw [fruchtShift_inl, fruchtShift_inr, fruchtGraph_adj_inl_inr,
        fruchtGraph_adj_inl_inr]
      have h : (a * g)⁻¹ * (a * x) = g⁻¹ * x := by
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [h]
  | inr p =>
    obtain ⟨g, i⟩ := p
    cases w with
    | inl y =>
      rw [fruchtShift_inr, fruchtShift_inl, fruchtGraph_adj_inr_inl,
        fruchtGraph_adj_inr_inl]
      have h : (a * g)⁻¹ * (a * y) = g⁻¹ * y := by
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      rw [h]
    | inr q =>
      obtain ⟨h2, j⟩ := q
      rw [fruchtShift_inr, fruchtShift_inr, fruchtGraph_adj_inr_inr,
        fruchtGraph_adj_inr_inr]
      constructor
      · intro hh
        exact ⟨(mul_right_inj a).mpr hh.1, hh.2⟩
      · intro hh
        exact ⟨(mul_right_inj a).mp hh.1, hh.2⟩

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
