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
end SimpleGraph
