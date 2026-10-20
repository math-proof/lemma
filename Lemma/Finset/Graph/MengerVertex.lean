import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Graph.MengerVertex
open MetaMathlibExt
open MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted


/--
[menger_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MengerVertex.lean)
-/
@[path]
private lemma menger_vertex_eq
  :
-- imply
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : V),
    s ≠ t →
    ¬ G.Adj s t →
    ∃ n : ℕ,
    (∃ C : Finset V,
    C.card = n ∧
    s ∉ C ∧
    t ∉ C ∧
    (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C) ∧
    ∀ C' : Finset V, s ∉ C' → t ∉ C' →
    (∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C') → n ≤ C'.card) ∧
    ∃ P : Fin n → G.Walk s t,
    (∀ i, (P i).support.Nodup) ∧
    (∀ i j, i ≠ j → ∀ v, v ∈ (P i).support → v ∈ (P j).support → v = s ∨ v = t) ∧
    ∀ (m : ℕ) (Q : Fin m → G.Walk s t),
    (∀ i, (Q i).support.Nodup) →
    (∀ i j, i ≠ j → ∀ v, v ∈ (Q i).support → v ∈ (Q j).support → v = s ∨ v = t) →
    m ≤ n := by
-- proof
  apply MetaMathlibExt.menger_vertex

/--
[isSTVertexCut_iff_walkSeparator](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MengerVertex.lean)
-/
@[path]
private lemma isSTVertexCut_iff_walkSeparator_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {s t : V}
  {C : Finset V} :
-- imply
  IsSTVertexCut G s t C ↔
    s ∉ C ∧ t ∉ C ∧ ∀ p : G.Walk s t, ∃ v ∈ p.support, v ∈ C := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted.isSTVertexCut_iff_walkSeparator G s t C

/--
[menger_vertex_max_min](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MengerVertex.lean)
-/
@[path]
private lemma menger_vertex_max_min_eq
  [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {s t : V}
-- given
  (hst : s ≠ t)
  (hadj : ¬ G.Adj s t) :
-- imply
  ∃ k : ℕ, ∃ (paths : Fin k → G.Path s t) (C : Finset V),
    IsInternallyVertexDisjointSTPaths paths ∧
    IsSTVertexCut G s t C ∧
    C.card = k ∧
    (∀ {l : ℕ} (paths' : Fin l → G.Path s t),
    IsInternallyVertexDisjointSTPaths paths' → l ≤ k) ∧
    (∀ C' : Finset V, IsSTVertexCut G s t C' → k ≤ C'.card) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted.menger_vertex_max_min s t hst hadj


-- created on 2026-10-20
