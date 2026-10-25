/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Chain
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Def.Combinatorics.RoadColoring.Part2
/-!
# Road coloring theorem

This file proves the road coloring theorem of A. N. Trahtman, "The road coloring problem",
Israel J. Math. 172 (2009) 51–60. The proof follows the reduction of Culik, Karhumäki and Kari:
a recoloring with a stable pair passes to a smaller quotient automaton, and synchronizing words
lift back. Stable pairs come from two bunches into one vertex, or else from Trahtman's lemma on
spanning subgraphs with a unique highest tree, via Kari's minimal-rank argument.
-/


namespace MetaMathlibExt

section

namespace RoadColoring

theorem rc_level_exists {V : Type*} [Finite V] (g : V → V) (v : V) :
    ∃ i : ℕ, g^[i] v ∈ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hstep : ∀ a b : ℕ, g^[a] v = g^[b] v → a < b →
      g^[b - a] (g^[a] v) = g^[a] v := by
    intro a b heq hab
    have hd : b = a + (b - a) := by omega
    have e : g^[a + (b - a)] v = g^[b - a] (g^[a] v) := by
      rw [Nat.add_comm a (b - a)]
      exact Function.iterate_add_apply g (b - a) a v
    have hper : g^[b - a] (g^[a] v) = g^[a] v := by
      rw [← e, ← hd]
      exact heq.symm
    exact hper
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) => g^[i.1] v) (by
      rw [Fintype.card_fin]
      omega)
  have hxy : x.1 ≠ y.1 := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact ⟨x.1, Function.mem_periodicPts.mpr
      ⟨y.1 - x.1, by omega, hstep x.1 y.1 heq hlt⟩⟩
  · exact ⟨y.1, Function.mem_periodicPts.mpr
      ⟨x.1 - y.1, by omega, hstep y.1 x.1 heq.symm hlt⟩⟩

end RoadColoring
end
end MetaMathlibExt
