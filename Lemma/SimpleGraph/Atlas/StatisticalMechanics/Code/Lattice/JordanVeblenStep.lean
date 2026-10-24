import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanVeblenStep
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jvp_consSpanningCoe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_consSpanningCoe_eq
  {G : SimpleGraph V}
  {x z y : V}
  {p : G.Walk z y}
-- given
  (hadj : G.Adj x z) :
-- imply
  (Walk.cons hadj p).toSubgraph.spanningCoe = p.toSubgraph.spanningCoe ⊔ edge x z := by
-- proof
  apply StatMech.Lattice.jvp_consSpanningCoe hadj p

/--
[jvp_sup_nil_spanningCoe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_sup_nil_spanningCoe_eq
  {G : SimpleGraph V}
  {x : V}
  {H : SimpleGraph V} :
-- imply
  H ⊔ (Walk.nil : G.Walk x x).toSubgraph.spanningCoe = H := by
-- proof
  apply StatMech.Lattice.jvp_sup_nil_spanningCoe x H

/--
[jvp_addWalk_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_addWalk_faceCount_eq
  [Empty.Finite V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  ∀ {x y : V} (q : G.Walk x y) (H : SimpleGraph V), q.IsPath → (∀ u ∈ q.support, ∀ w, ¬ H.Adj u w) → faceCount (H ⊔ q.toSubgraph.spanningCoe) = faceCount H ∧ (∀ u ∈ q.support, (H ⊔ q.toSubgraph.spanningCoe).Reachable x u) := by
-- proof
  apply StatMech.Lattice.jvp_addWalk_faceCount

/--
[jvp_faceCount_deleteCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_faceCount_deleteCycle_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [LocallyFinite K]
  {v : V}
  {p : K.Walk v v}
-- given
  (hcyc : K.IsCycles)
  (hp : p.IsCycle) :
-- imply
  faceCount (K.deleteEdges p.toSubgraph.edgeSet) + 1 = faceCount K := by
-- proof
  apply StatMech.Lattice.jvp_faceCount_deleteCycle K hcyc p hp

/--
[jvp_isCycles_deleteCycle_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_isCycles_deleteCycle_isCycles_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [LocallyFinite K]
  {v : V}
  {p : K.Walk v v}
-- given
  (hcyc : K.IsCycles)
  (hp : p.IsCycle) :
-- imply
  (K.deleteEdges p.toSubgraph.edgeSet).IsCycles := by
-- proof
  apply StatMech.Lattice.jvp_isCycles_deleteCycle_isCycles hcyc p hp

/--
[jvp_ncard_deleteCycle_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_ncard_deleteCycle_lt_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  {v : V}
  {p : K.Walk v v}
-- given
  (hp : p.IsCycle) :
-- imply
  (K.deleteEdges p.toSubgraph.edgeSet).edgeSet.ncard < K.edgeSet.ncard := by
-- proof
  apply StatMech.Lattice.jvp_ncard_deleteCycle_lt p hp

/--
[jvp_isCycles_veblenStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_isCycles_veblenStep_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [LocallyFinite K]
-- given
  (hcyc : K.IsCycles)
  (hne : K.edgeSet.Nonempty) :
-- imply
  ∃ K' : SimpleGraph V, K' ≤ K ∧ K'.IsCycles ∧ K'.edgeSet.ncard < K.edgeSet.ncard ∧ faceCount K' + 1 = faceCount K := by
-- proof
  apply StatMech.Lattice.jvp_isCycles_veblenStep K hcyc hne

/--
[jvp_isCycles_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_isCycles_even_eq
  [Empty.Finite V]
  {K : SimpleGraph V}
  {v : V}
-- given
  (hcyc : K.IsCycles) :
-- imply
  Even (Nat.card (K.neighborSet v)) := by
-- proof
  apply StatMech.Lattice.jvp_isCycles_even hcyc v

/--
[jvp_veblen_note](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanVeblenStep.lean)
-/
@[path]
private lemma jvp_veblen_note_eq
  [Empty.Finite V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [LocallyFinite K]
-- given
  (hcyc : K.IsCycles)
  (hne : K.edgeSet.Nonempty) :
-- imply
  (∃ K' : SimpleGraph V, K' ≤ K ∧ K'.IsCycles ∧ K'.edgeSet.ncard < K.edgeSet.ncard ∧ faceCount K' + 1 = faceCount K) ∧ (∀ v : V, Even (Nat.card (K.neighborSet v))) := by
-- proof
  apply StatMech.Lattice.jvp_veblen_note K hcyc hne


-- created on 2026-10-23
