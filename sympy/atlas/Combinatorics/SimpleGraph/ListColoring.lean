/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# List colorings of simple graphs

This file provides basic predicates for vertex list colorability and choice
numbers. A list coloring is represented by a Mathlib `SimpleGraph.Coloring`
whose value at each vertex belongs to that vertex's finite list of colors.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {q r : ℕ}

/-- A graph is `q`-list-colorable if every assignment of at least `q` colors to
each vertex admits a proper coloring chosen from those lists. -/
def IsListColorable (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∀ (C : Type) [DecidableEq C] (lists : V → Finset C),
    (∀ v, q ≤ (lists v).card) →
      ∃ color : G.Coloring C, ∀ v, color v ∈ lists v

/-- `q` is the choice number of `G` if `G` is `q`-list-colorable but is not
list-colorable with any smaller number of colors. -/
def IsChoiceNumber (G : SimpleGraph V) (q : ℕ) : Prop :=
  G.IsListColorable q ∧ ∀ r < q, ¬G.IsListColorable r

/-- List colorability is monotone in the number of colors required in each list. -/
theorem IsListColorable.mono (hG : G.IsListColorable q) (hqr : q ≤ r) :
    G.IsListColorable r := by
  intro C _ lists hlists
  exact hG C lists fun v => hqr.trans (hlists v)

/-- A list-colorable graph is colorable with the same number of colors. -/
theorem IsListColorable.colorable (hG : G.IsListColorable q) : G.Colorable q := by
  let lists : V → Finset (Fin q) := fun _ => Finset.univ
  obtain ⟨color, _⟩ := hG (Fin q) lists (by simp [lists])
  exact ⟨color⟩

end SimpleGraph
