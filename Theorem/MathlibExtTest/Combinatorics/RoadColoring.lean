/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/RoadColoring.lean -/


import Theorem.Combinatorics.RoadColoring.Part8
import Lemma.Finset.RoadColoring


namespace MetaMathlibExt

-- `roadColoring'` applies with only a `Finite` instance in context.
example {V : Type*} [Finite V] [Nonempty V] (Adj : V → V → Prop)
    (hcon : ∀ u v : V, Relation.ReflTransGen Adj u v)
    (haper : ∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
      List.IsChain Adj (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length))
    (hreg : ∃ k : ℕ, 0 < k ∧ ∀ v : V, Nonempty ({ w : V // Adj v w } ≃ Fin k)) :
    ∃ (k : ℕ) (trans : V → Fin k → V),
      (∀ v : V, ∀ c : Fin k, Adj v (trans v c)) ∧
      (∀ v : V, Function.Injective (trans v)) ∧
      (∀ (v w : V), Adj v w → ∃ c : Fin k, trans v c = w) ∧
      ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl trans v word = r :=
  roadColoring' Adj hcon haper hreg

-- `roadColoring` applies with a `Fintype` instance.
example {V : Type*} [Fintype V] [Nonempty V] (Adj : V → V → Prop)
    (hcon : ∀ u v : V, Relation.ReflTransGen Adj u v)
    (haper : ∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
      List.IsChain Adj (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length))
    (hreg : ∃ k : ℕ, 0 < k ∧ ∀ v : V, Nonempty ({ w : V // Adj v w } ≃ Fin k)) :
    ∃ (k : ℕ) (trans : V → Fin k → V),
      (∀ v : V, ∀ c : Fin k, Adj v (trans v c)) ∧
      (∀ v : V, Function.Injective (trans v)) ∧
      (∀ (v w : V), Adj v w → ∃ c : Fin k, trans v c = w) ∧
      ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl trans v word = r :=
  roadColoring Adj hcon haper hreg

end MetaMathlibExt
