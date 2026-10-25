/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Fin
import Instance.Combinatorics.SimpleGraph.Frucht


section

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

def fruchtAdj (N : ℕ) {G : Type*} [Group G] [DecidableEq G] (e : G ≃ Fin N) :
    (G ⊕ (G × Fin N)) → (G ⊕ (G × Fin N)) → Prop
  | .inl x, .inl y => x ≠ y
  | .inl x, .inr (g, j) => e (g⁻¹ * x) ≤ j
  | .inr (g, j), .inl x => e (g⁻¹ * x) ≤ j
  | .inr (g, i), .inr (h, j) => g = h ∧ i ≠ j

noncomputable def fruchtGraph (N : ℕ) {G : Type*} [Group G] [DecidableEq G] [Fintype G]
    (e : G ≃ Fin N) : SimpleGraph (G ⊕ (G × Fin N)) where
  Adj := fruchtAdj N e
  symm := Std.Symm.mk (fun a b h => by
    cases a with
    | inl x =>
      cases b with
      | inl y => exact Ne.symm h
      | inr p => obtain ⟨g, j⟩ := p; exact h
    | inr p =>
      obtain ⟨g, i⟩ := p
      cases b with
      | inl y => exact h
      | inr q => obtain ⟨h2, j⟩ := q; exact ⟨Eq.symm h.1, Ne.symm h.2⟩)
  loopless := Std.Irrefl.mk (fun a h => by
    cases a with
    | inl x => exact absurd rfl h
    | inr p => obtain ⟨g, j⟩ := p; exact absurd rfl h.2)

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted
end
