/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/RobbinsTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.CompletePartialOrder
import Mathlib.SetTheory.Cardinal.NatCard


section

namespace MetaMathlibExt

/-- A partial orientation is "good" if it only uses graph edges, is
antisymmetric, and every oriented edge has both endpoints in the strong
component of `r`. -/
def GoodOr {V : Type*} (G : SimpleGraph V) (r : V) (D : V → V → Prop) : Prop :=
  (∀ x y, D x y → G.Adj x y) ∧
  (∀ x y, D x y → D y x → False) ∧
  (∀ x y, D x y → (Relation.ReflTransGen D r x ∧ Relation.ReflTransGen D x r) ∧
    (Relation.ReflTransGen D r y ∧ Relation.ReflTransGen D y r))

/-- The predicate maximized in the ear-decomposition argument. -/
def RobbinsPred {V : Type*} [Finite V] (G : SimpleGraph V) (r : V) : ℕ → Prop :=
  fun k => ∃ D : V → V → Prop, GoodOr G r D ∧
    k ≤ Set.ncard {v | Relation.ReflTransGen D r v ∧ Relation.ReflTransGen D v r}

end MetaMathlibExt
end
