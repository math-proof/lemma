import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Graph.RobbinsTheorem
open MetaMathlibExt


/--
[robbins_theorem_connected](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/RobbinsTheorem.lean)
-/
@[path]
private lemma robbins_theorem_connected_eq
  [Finite V] [Nonempty V]
  {G : SimpleGraph V} :
-- imply
  (G.Connected ∧
    ∀ u v, G.Adj u v →
    ∀ a b, Relation.ReflTransGen
    (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) a b) ↔
    ∃ D : V → V → Prop, (∀ u v, D u v → G.Adj u v) ∧
    (∀ u v, G.Adj u v → Xor (D u v) (D v u)) ∧
    (∀ u v, Relation.ReflTransGen D u v) := by
-- proof
  apply MetaMathlibExt.robbins_theorem_connected G

/--
[robbins_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/RobbinsTheorem.lean)
-/
@[path]
private lemma robbins_theorem_eq
  [Finite V]
  {G : SimpleGraph V} :
-- imply
  ((∀ u v, G.Reachable u v) ∧
    ∀ u v, G.Adj u v →
    ∀ a b, Relation.ReflTransGen
    (fun x y => G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) a b) ↔
    ∃ D : V → V → Prop, (∀ u v, D u v → G.Adj u v) ∧
    (∀ u v, G.Adj u v → Xor (D u v) (D v u)) ∧
    (∀ u v, Relation.ReflTransGen D u v) := by
-- proof
  apply MetaMathlibExt.robbins_theorem G


-- created on 2026-10-20
