import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.Part3
open StatMech StatMech.Ising


/--
[finiteFiberMultiplicityCode_key_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.lean)
-/
@[path]
private lemma finiteFiberMultiplicityCode_key_injective_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype S]
  [Fintype T]
-- given
  (key : S -> T)
  (hfiber : forall target, Fintype.card {s : S // key s = target} <= 2) :
-- imply
  Function.Injective (fun s => (finiteFiberMultiplicityCode key hfiber s, key s)) := by
-- proof
  apply StatMech.Ising.finiteFiberMultiplicityCode_key_injective key hfiber

/--
[lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers_not_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.lean)
-/
@[path]
private lemma lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers_not_strict_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype S]
  {G : SimpleGraph V}
  {s : S}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
  (hfiber : forall target, Fintype.card {s : S // key s = target} <= 2)
  (hnonstrict : forall s, ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q ⟨0, key s⟩) :
-- imply
  ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q (lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers G sites q key hfiber s) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateHandledEmbeddingOfNonstrictKeyFibers_not_strict G sites q key hfiber hnonstrict s


-- created on 2026-10-23
