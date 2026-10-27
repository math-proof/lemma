import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPartialReflectDecorated.Part2
open Finset StatMech StatMech.Ising


/--
[lpReplica_cast_subtype_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPartialReflectDecorated.lean)
-/
@[path]
private lemma lpReplica_cast_subtype_val_eq
  [Fintype V]
  [DecidableEq V]
  {a b : J}
  {x : {y : F a // P a y}}
-- given
  (F : J -> Type*)
  (P : ∀ j, F j -> Prop)
  (h : a = b) :
-- imply
  (cast (congrArg (fun j => {y : F j // P j y}) h) x).1 = cast (congrArg F h) x.1 := by
-- proof
  apply StatMech.Ising.lpReplica_cast_subtype_val F P h x

/--
[lpReplicaPartialReflectDecoratedTraceMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPartialReflectDecorated.lean)
-/
@[path]
private lemma lpReplicaPartialReflectDecoratedTraceMap_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (lpReplicaPartialReflectDecoratedTraceMap G sites hsite hij q) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectDecoratedTraceMap_injective G sites hsite hij q


-- created on 2026-10-23
