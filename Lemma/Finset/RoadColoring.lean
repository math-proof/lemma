import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.RoadColoring
open MetaMathlibExt


/--
[roadColoring'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma roadColoring'_eq
  :
-- imply
  ∀ {V : Type*} [Finite V] [Nonempty V]
    (Adj : V → V → Prop),
    (∀ u v : V, Relation.ReflTransGen Adj u v) →
    (∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
    List.IsChain Adj (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length)) →
    (∃ k : ℕ, 0 < k ∧ ∀ v : V, Nonempty ({ w : V // Adj v w } ≃ Fin k)) →
    ∃ (k : ℕ) (trans : V → Fin k → V),
    (∀ v : V, ∀ c : Fin k, Adj v (trans v c)) ∧
    (∀ v : V, Function.Injective (trans v)) ∧
    (∀ (v w : V), Adj v w → ∃ c : Fin k, trans v c = w) ∧
    ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl trans v word = r := by
-- proof
  apply MetaMathlibExt.roadColoring'

/--
[roadColoring](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/RoadColoring.lean)
-/
@[path]
private lemma roadColoring_eq
  :
-- imply
  ∀ {V : Type*} [Fintype V] [Nonempty V]
    (Adj : V → V → Prop),
    (∀ u v : V, Relation.ReflTransGen Adj u v) →
    (∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
    List.IsChain Adj (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length)) →
    (∃ k : ℕ, 0 < k ∧ ∀ v : V, Nonempty ({ w : V // Adj v w } ≃ Fin k)) →
    ∃ (k : ℕ) (trans : V → Fin k → V),
    (∀ v : V, ∀ c : Fin k, Adj v (trans v c)) ∧
    (∀ v : V, Function.Injective (trans v)) ∧
    (∀ (v w : V), Adj v w → ∃ c : Fin k, trans v c = w) ∧
    ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl trans v word = r := by
-- proof
  apply MetaMathlibExt.roadColoring


-- created on 2026-10-20
