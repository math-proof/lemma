import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCurrentGraph
open Finset StatMech StatMech.Ising


/--
[lpReplicaCurrentReflect_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_left_eq
  [Fintype V]
  [DecidableEq V]
  {x : V} :
-- imply
  lpReplicaCurrentReflect (.inl (.inl x)) = .inl (.inr x) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_left x

/--
[lpReplicaCurrentReflect_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_right_eq
  [Fintype V]
  [DecidableEq V]
  {x : V} :
-- imply
  lpReplicaCurrentReflect (.inl (.inr x)) = .inl (.inl x) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_right x

/--
[lpReplicaCurrentReflect_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {b : Bool} :
-- imply
  lpReplicaCurrentReflect (.inr b : LPReplicaCurrentVertex V) = .inr (!b) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_ghost b

/--
[lpReplicaCurrentReflect_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_involutive_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  Function.Involutive (lpReplicaCurrentReflect (V := V)) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_involutive

/--
[lpReplicaCurrentRel_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentRel_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V) :
-- imply
  lpReplicaCurrentRel G sites (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) <-> lpReplicaCurrentRel G sites x y := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentRel_reflect G sites x y

/--
[lpReplicaCurrentGraph_adj_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentGraph_adj_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentGraph G sites).Adj (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) <-> (lpReplicaCurrentGraph G sites).Adj x y := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGraph_adj_reflect G sites x y

/--
[lpReplicaCurrentCoupling_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentCoupling_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {r : Real}
  {e : Sym2 (LPReplicaCurrentVertex V)}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  lpReplicaCurrentCoupling J hf r (Sym2.map lpReplicaCurrentReflect e) = lpReplicaCurrentCoupling J hf r e := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCoupling_reflect J hf r e

/--
[lpReplicaCurrentCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {r : Real}
  {e : Sym2 (LPReplicaCurrentVertex V)}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r) :
-- imply
  0 <= lpReplicaCurrentCoupling J hf r e := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr e

/--
[lpReplicaCurrentGraph_adj_left_right_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentGraph_adj_left_right_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : V}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentGraph G sites).Adj (.inl (.inl x)) (.inl (.inr y)) <-> ∃ i, sites i = x ∧ sites i = y := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGraph_adj_left_right_iff G sites x y

/--
[lpReplicaCurrentSeamEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentSeamEdge_injective_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites) :
-- imply
  Function.Injective (lpReplicaCurrentSeamEdge sites) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentSeamEdge_injective sites hsite

/--
[lpReplicaCurrentSeamEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCurrentGraph.lean)
-/
@[path]
private lemma lpReplicaCurrentSeamEdge_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i : I}
-- given
  (sites : I -> V) :
-- imply
  lpReplicaCurrentSeamEdge sites i ∈ (lpReplicaCurrentGraph G sites).edgeFinset := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentSeamEdge_mem G sites i


-- created on 2026-10-23
