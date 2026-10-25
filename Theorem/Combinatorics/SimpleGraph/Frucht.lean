/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Instance.Combinatorics.SimpleGraph.Frucht.Part2


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

theorem fruchtGraph_adj_inl_inl (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (x y : G) :
    (fruchtGraph N e).Adj (.inl x) (.inl y) ↔ x ≠ y := Iff.rfl

theorem fruchtGraph_adj_inl_inr (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (x g : G) (j : Fin N) :
    (fruchtGraph N e).Adj (.inl x) (.inr (g, j)) ↔ e (g⁻¹ * x) ≤ j := Iff.rfl

theorem fruchtGraph_adj_inr_inl (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (g x : G) (j : Fin N) :
    (fruchtGraph N e).Adj (.inr (g, j)) (.inl x) ↔ e (g⁻¹ * x) ≤ j := Iff.rfl

theorem fruchtGraph_adj_inr_inr (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) (g h : G) (i j : Fin N) :
    (fruchtGraph N e).Adj (.inr (g, i)) (.inr (h, j)) ↔ g = h ∧ i ≠ j := Iff.rfl

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
