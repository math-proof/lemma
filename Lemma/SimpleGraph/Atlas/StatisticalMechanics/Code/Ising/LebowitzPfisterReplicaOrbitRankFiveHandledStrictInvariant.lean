import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
open StatMech StatMech.Ising


/--
[lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
  {x₀ x₁ : LPReplicaOrbitCommonSlot G sites q}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hxx : x₀ ≠ x₁)
  (hx₀ : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q y x₀)
  (hx₁ : LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q y x₁)
  (hzy : LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z y) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).card = 2 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteCandidates_card_eq_two_of_two_spatialWitnesses G sites hsite q hcard y x₀ x₁ hxx hx₀ hx₁ z hzy

/--
[lpReplicaAggregateDecoratedTargetSlotState_toAggregate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetSlotState_toAggregate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {y : LPReplicaOffdiagDecoratedTarget G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedTargetSlotState G sites q (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y) = (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetSlotState_toAggregate G sites i j q y

/--
[lpReplicaRankFiveMarkedOutputData_hasStrictPhysicalDoubleIncidence_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveMarkedOutputData_hasStrictPhysicalDoubleIncidence_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hthree : (lpReplicaCurrentCopies G sites z.1.1.1 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false).card = 3) :
-- imply
  LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output ↔ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites z.1.1.1 (lpReplicaRowCopies G sites z.1.1.1 (lpReplicaToggleRows G sites z.1.1.1 {d.copy} (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) true) := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveMarkedOutputData_hasStrictPhysicalDoubleIncidence_iff G sites hsite hij q hcard z hthree d

/--
[lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_exists_parallelPhysicalPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_exists_parallelPhysicalPair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
  (hstrict : LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output) :
-- imply
  let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false ∃ c e, c ≠ e ∧ Finset.univ \ K = {c, e} ∧ ¬ (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_exists_parallelPhysicalPair G sites hsite hij q hcard z hhigh d hstrict

/--
[lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
  (hstrict : LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output) :
-- imply
  ∃ x₀ x₁ : LPReplicaOrbitCommonSlot G sites q, x₀ ≠ x₁ ∧ LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output) x₀ ∧ LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output) x₁ := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveNonsaturatedHighMarkedOutput_strict_two_spatialWitnesses G sites hsite hij q hcard z hhigh d hstrict

/--
[lpReplicaRankFiveNonsaturatedHighMarkedOutput_incoming_degree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveNonsaturatedHighMarkedOutput_incoming_degree_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
  {w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
  (hstrict : LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output)
  (hrelated : LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard w (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output)) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q w).card = 2 := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveNonsaturatedHighMarkedOutput_incoming_degree_two G sites hsite hij q hcard z hhigh d hstrict w hrelated

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Function.Injective (fun d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z) => lpReplicaAggregateDecoratedTargetSlotState G sites q (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget G sites hsite q hcard z d)) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_slotState_injective G sites hsite q hcard z

/--
[lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y ≠ y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetFlipMultiplicity_ne G sites q y

/--
[lpReplicaAggregateDecoratedTargetFlipMultiplicity_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetFlipMultiplicity_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) = y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetFlipMultiplicity_involutive G sites q y

/--
[lpReplicaAggregateDecoratedTargetFlipMultiplicity_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetFlipMultiplicity_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaAggregateDecoratedTargetSlotState G sites q (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) = lpReplicaAggregateDecoratedTargetSlotState G sites q y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetFlipMultiplicity_slotState G sites q y

/--
[lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
  {x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) x ↔ LPReplicaAggregateRankFiveStrictRouteTargetSpatialWitness G sites q y x := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteTargetSpatialWitness_flip_iff G sites q y x

/--
[lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incoming_degree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incoming_degree_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
  {w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
  (hstrict : LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output)
  (hrelated : LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard w (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output))) :
-- imply
  (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q w).card = 2 := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incoming_degree_two G sites hsite hij q hcard z hhigh d hstrict w hrelated

/--
[lpReplicaRankFiveNonsaturatedHighMarkedOutput_incomingDegree_one_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveNonsaturatedHighMarkedOutput_incomingDegree_one_eq_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
  (hstrict : LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 1 (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output) = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveNonsaturatedHighMarkedOutput_incomingDegree_one_eq_empty G sites hsite hij q hcard z hhigh d hstrict

/--
[lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incomingDegree_one_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incomingDegree_one_eq_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
  (hstrict : LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 1 (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output)) = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveNonsaturatedHighMarkedOutput_flip_incomingDegree_one_eq_empty G sites hsite hij q hcard z hhigh d hstrict

/--
[lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_eq_half_incomingDegreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_eq_half_incomingDegreeTwo_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
  (hstrict : LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output) :
-- imply
  (∑ w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q, LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard w (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output)) = ((LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 2 (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output)).card : Real) / 2 := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_eq_half_incomingDegreeTwo G sites hsite hij q hcard z hhigh d hstrict

/--
[lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_lt_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_lt_one_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hhigh : let data := lpReplicaDecoratedSourceRowGateData G sites i j q z let K := lpReplicaCurrentCopies G sites z.1.1.1 data.1 true false K.card = 3 ∧ ∃ r, r ∈ Finset.univ \ K ∧ (data.1 r).1 = true)
  (hstrict : LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output) :
-- imply
  (∑ w : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q, LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard w (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output)) < 1 ↔ (LPReplicaAggregateRankFiveStrictRouteIncomingDegree G sites hsite q hcard 2 (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q d.output)).card ≤ 1 := by
-- proof
  apply StatMech.Ising.lpReplicaRankFiveNonsaturatedHighMarkedOutput_targetLoad_lt_one_iff G sites hsite hij q hcard z hhigh d hstrict

/--
[lpReplicaAggregateDecoratedTargetFlipMultiplicity_hasStrictPhysicalDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTargetFlipMultiplicity_hasStrictPhysicalDoubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) ↔ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites q y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTargetFlipMultiplicity_hasStrictPhysicalDoubleIncidence G sites q y

/--
[lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hzy : LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z y)
  (hdegree : (lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates G sites hsite q z).card = 2) :
-- imply
  ∃ y', LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z y' ∧ y' ≠ y ∧ y' ≠ lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRoute_exists_alternateTarget G sites hsite q hcard z y hzy hdegree

/--
[lpReplicaAggregateDecoratedTarget_card_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTarget_card_ge_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  2 ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTarget_card_ge_two G sites q y

/--
[lpReplicaAggregateDecoratedTarget_card_ge_three_of_alternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateDecoratedTarget_card_ge_three_of_alternate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y y' : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hy'y : y' ≠ y)
  (hy'flip : y' ≠ lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) :
-- imply
  3 ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateDecoratedTarget_card_ge_three_of_alternate G sites q y y' hy'y hy'flip

/--
[lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  1 + (LPReplicaAggregateRankFiveStrictRouteIncoming G sites hsite q hcard y).card ≤ Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_target G sites hsite q hcard y

/--
[lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
  {y y' : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hzy : LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z y)
  (hzy' : LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z y') :
-- imply
  y.2.1 = y'.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRelated_selectedSeam_eq G sites hsite q hcard z y y' hzy hzy'

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y y' : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hy' : y' ∈ LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood G sites hsite q hcard y) :
-- imply
  y'.2.1 = y.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_selectedSeam G sites hsite q hcard y y' hy'

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_disjoint_of_selectedSeam_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_disjoint_of_selectedSeam_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y w : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hseam : y.2.1 ≠ w.2.1) :
-- imply
  Disjoint (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood G sites hsite q hcard y) (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood G sites hsite q hcard w) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_disjoint_of_selectedSeam_ne G sites hsite q hcard y w hseam

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteGraph_adj_selectedSeam_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteGraph_adj_selectedSeam_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y w : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph G sites hsite q hcard).Adj y w) :
-- imply
  y.2.1 = w.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteGraph_adj_selectedSeam_eq G sites hsite q hcard hyw

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteGraph_reachable_selectedSeam_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteGraph_reachable_selectedSeam_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y w : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph G sites hsite q hcard).Reachable y w) :
-- imply
  y.2.1 = w.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteGraph_reachable_selectedSeam_eq G sites hsite q hcard hyw

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_subset_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_subset_component_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood G sites hsite q hcard y ⊆ LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteNeighborhood_subset_component G sites hsite q hcard y

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteComponent_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteComponent_eq_of_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y w : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hyw : (LPReplicaAggregateRankFiveStrictRouteRerouteGraph G sites hsite q hcard).Reachable y w) :
-- imply
  LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y = LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard w := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteComponent_eq_of_reachable G sites hsite q hcard y w hyw

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_not_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y w : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hyw : ¬ (LPReplicaAggregateRankFiveStrictRouteRerouteGraph G sites hsite q hcard).Reachable y w) :
-- imply
  Disjoint (LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y) (LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard w) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_not_reachable G sites hsite q hcard y w hyw

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_selectedSeam_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_selectedSeam_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y w : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hseam : y.2.1 ≠ w.2.1) :
-- imply
  Disjoint (LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y) (LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard w) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteComponent_disjoint_of_selectedSeam_ne G sites hsite q hcard y w hseam

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteComponent_flip_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteComponent_flip_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y t : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y) :
-- imply
  lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteComponent_flip_mem G sites hsite q hcard y t ht

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y t w : LPReplicaAggregateDecoratedTarget G sites q}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y)
  (hzt : LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z t)
  (hzw : LPReplicaAggregateRankFiveStrictRouteRelated G sites hsite q hcard z w) :
-- imply
  w ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteComponent_related_mem G sites hsite q hcard y t w z ht hzt hzw

/--
[lpReplicaAggregateRankFiveStrictRouteRerouteComponentSources_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRouteRerouteComponentSources_card_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  (LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources G sites hsite q hcard y).card ≤ (LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y).card := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRouteRerouteComponentSources_card_le G sites hsite q hcard y

/--
[lpReplicaAggregateRankFiveStrictRoute_one_add_componentSources_card_le_of_targetLoad_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRoute_one_add_componentSources_card_le_of_targetLoad_lt_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y t : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (ht : t ∈ LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y)
  (hslack : (∑ z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q, LPReplicaAggregateRankFiveStrictRouteWeight G sites hsite q hcard z t) < 1) :
-- imply
  1 + (LPReplicaAggregateRankFiveStrictRouteRerouteComponentSources G sites hsite q hcard y).card ≤ (LPReplicaAggregateRankFiveStrictRouteRerouteComponent G sites hsite q hcard y).card := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRoute_one_add_componentSources_card_le_of_targetLoad_lt_one G sites hsite q hcard y t ht hslack

/--
[lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y y' : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hy' : y' = y ∨ y' = lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y) :
-- imply
  y' ∈ LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood G sites hsite q hcard y := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRoute_pair_subset_rerouteNeighborhood G sites hsite q hcard y y' hy'

/--
[lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_rerouteNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_rerouteNeighborhood_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {y : LPReplicaAggregateDecoratedTarget G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  1 + (LPReplicaAggregateRankFiveStrictRouteIncoming G sites hsite q hcard y).card ≤ (LPReplicaAggregateRankFiveStrictRouteRerouteNeighborhood G sites hsite q hcard y).card := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateRankFiveStrictRoute_one_add_incoming_card_le_rerouteNeighborhood G sites hsite q hcard y

/--
[lpReplicaLowRowMarkedOutputData_not_hasStrictPhysicalDoubleIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean)
-/
@[path]
private lemma lpReplicaLowRowMarkedOutputData_not_hasStrictPhysicalDoubleIncidence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {d : LPReplicaLowRowMarkedOutputData G sites q z}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
  (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z) :
-- imply
  ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence G sites i j q d.output := by
-- proof
  apply StatMech.Ising.lpReplicaLowRowMarkedOutputData_not_hasStrictPhysicalDoubleIncidence G sites hsite hij q hcard z hlow d


-- created on 2026-10-23
