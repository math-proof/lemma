/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean -/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

/-!
# Odd independent sets

Source: Martin Knor, Jelena Sedlar, and Riste Škrekovski,
*On the odd independence number of the Queen graph* (arXiv:2608.19024v1),
lines 91-94. A set `S` is odd independent when it is independent and every
outside vertex sees an empty or odd-sized open-neighbourhood intersection.
The odd independence number itself is not defined here.
-/

namespace SimpleGraph

variable {V : Type*}

/-- Odd independent set: independent `S` such that every `v ∉ S` meets `S`
in an empty or finite odd-sized open neighbourhood. -/
def IsOddIndependent (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsIndepSet S ∧
    ∀ v : V, v ∉ S →
      (G.neighborSet v ∩ S).Finite ∧
        ((G.neighborSet v ∩ S) = ∅ ∨ Odd (G.neighborSet v ∩ S).ncard)

/-- Independence projection of an odd independent set. -/
theorem IsOddIndependent.isIndepSet {G : SimpleGraph V} {S : Set V}
    (h : G.IsOddIndependent S) : G.IsIndepSet S :=
  h.1

/-- Finiteness of each outside-neighbourhood intersection. -/
theorem IsOddIndependent.finite_inter {G : SimpleGraph V} {S : Set V}
    (h : G.IsOddIndependent S) (v : V) (hv : v ∉ S) :
    (G.neighborSet v ∩ S).Finite :=
  (h.2 v hv).1

/-- Empty-or-odd alternative for each outside intersection. -/
theorem IsOddIndependent.empty_or_odd {G : SimpleGraph V} {S : Set V}
    (h : G.IsOddIndependent S) (v : V) (hv : v ∉ S) :
    (G.neighborSet v ∩ S) = ∅ ∨ Odd (G.neighborSet v ∩ S).ncard :=
  (h.2 v hv).2

/-- The empty set is odd independent in any simple graph. -/
theorem isOddIndependent_empty {G : SimpleGraph V} :
    G.IsOddIndependent ∅ := by
  refine ⟨fun u hu => absurd hu (Set.notMem_empty u), fun v _ => ?_⟩
  rw [Set.inter_empty]
  exact ⟨Set.finite_empty, Or.inl rfl⟩

/-- Every singleton is odd independent in any simple graph. -/
theorem isOddIndependent_singleton {G : SimpleGraph V} (a : V) :
    G.IsOddIndependent {a} := by
  constructor
  · intro u hu w hw hne
    rw [Set.mem_singleton_iff] at hu hw
    exact absurd (hu.trans hw.symm) hne
  · intro v _
    have hfin : (G.neighborSet v ∩ {a}).Finite :=
      Set.Finite.subset (Set.finite_singleton a) Set.inter_subset_right
    refine ⟨hfin, ?_⟩
    by_cases ha : a ∈ G.neighborSet v
    · have heq : G.neighborSet v ∩ {a} = {a} := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · intro hx
          exact hx.2
        · intro hx
          rw [hx]
          exact ⟨ha, rfl⟩
      rw [heq, Set.ncard_singleton]
      exact Or.inr odd_one
    · have hempty : G.neighborSet v ∩ {a} = ∅ := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_inter_iff, Set.mem_singleton_iff] at hx
          exact absurd (hx.2 ▸ hx.1) ha
        · intro hx
          exact absurd hx (Set.notMem_empty x)
      exact Or.inl hempty

end SimpleGraph
