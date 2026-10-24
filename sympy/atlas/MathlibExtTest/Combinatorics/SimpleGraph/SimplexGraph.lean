/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/SimplexGraph.lean -/


import sympy.atlas.Combinatorics.SimpleGraph.SimplexGraph
import Lemma.SimpleGraph.SimplexGraph

open scoped symmDiff

example : SimpleGraph.SimplexVertex (⊥ : _root_.SimpleGraph (Fin 2)) :=
  SimpleGraph.emptyVertex _

example :
    (SimpleGraph.emptyVertex (⊥ : _root_.SimpleGraph (Fin 2))).1 = ∅ :=
  rfl

example (v : Fin 2) :
    (SimpleGraph.singletonVertex (⊥ : _root_.SimpleGraph (Fin 2)) v).1 = {v} :=
  rfl

example (v : Fin 2) :
    (SimpleGraph.simplexGraph (⊥ : _root_.SimpleGraph (Fin 2))).Adj
      (SimpleGraph.emptyVertex _) (SimpleGraph.singletonVertex _ v) :=
  SimpleGraph.empty_adj_singleton _ _

example (v : Fin 2) :
    (SimpleGraph.simplexGraph (⊥ : _root_.SimpleGraph (Fin 2))).Adj
      (SimpleGraph.emptyVertex _) (SimpleGraph.singletonVertex _ v) ↔
      (((SimpleGraph.emptyVertex (⊥ : _root_.SimpleGraph (Fin 2))).1 ∆
        (SimpleGraph.singletonVertex (⊥ : _root_.SimpleGraph (Fin 2)) v).1).card =
        1) :=
  SimpleGraph.adj_iff _ _ _

example :
    ¬ (SimpleGraph.simplexGraph (⊥ : _root_.SimpleGraph (Fin 2))).Adj
      (SimpleGraph.singletonVertex _ 0) (SimpleGraph.singletonVertex _ 1) := by
  rw [SimpleGraph.adj_iff]
  decide

example :
    let pair : SimpleGraph.SimplexVertex (⊤ : _root_.SimpleGraph (Fin 2)) :=
      ⟨{0, 1}, by intro x _hx y _hy hne; simpa using hne⟩;
    pair.1 = {0, 1} ∧
      (SimpleGraph.simplexGraph (⊤ : _root_.SimpleGraph (Fin 2))).Adj pair
        (SimpleGraph.singletonVertex _ 0) :=
  ⟨rfl, (SimpleGraph.adj_iff _ _ _).2 (by decide)⟩
