/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual.Part2


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaAggregateRankFiveHandledTargetImage
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    (lpReplicaAggregateRankFiveHandledTargetImage
      G sites hsite q hcard).card =
      Fintype.card
        (LPReplicaAggregateLowOrResolvableHighSourceRankFive G sites q) := by
  classical
  unfold lpReplicaAggregateRankFiveHandledTargetImage
  rw [Finset.card_image_of_injective _
    (lpReplicaAggregateLowOrResolvableHighRankFiveEmbedding
      G sites hsite q hcard).injective,
    Finset.card_univ]


theorem lpReplicaAggregateRankFiveResidualCapacity_of_selected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (hselected : LPReplicaAggregateRankFiveSelectedResidualCapacity
      G sites hsite q hcard) :
    LPReplicaAggregateRankFiveResidualCapacity G sites q := by
  classical
  let A := LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q
  let used := lpReplicaAggregateRankFiveHandledTargetImage
    G sites hsite q hcard
  let B := {y : LPReplicaAggregateDecoratedTarget G sites q // y ∉ used}
  let f : A -> I := fun z =>
    lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q
      (z.toAggregate G sites q)
  let g : B -> I := fun y => y.1.2.1
  have hfiber : forall k : I,
      Fintype.card {z : A // f z = k} <=
        Fintype.card {y : B // g y = k} := by
    simpa only [LPReplicaAggregateRankFiveSelectedResidualCapacity,
      A, B, f, g, used] using hselected
  have hhall :=
    (Fintype.hall_equalFiber_iff_card_fibers f g).mpr hfiber
  have hAB : Fintype.card A <= Fintype.card B := by
    calc
      Fintype.card A = (Finset.univ : Finset A).card :=
        Finset.card_univ.symm
      _ <= (Finset.univ.filter fun b : B =>
          exists a, a ∈ (Finset.univ : Finset A) /\ f a = g b).card :=
        hhall Finset.univ
      _ <= (Finset.univ : Finset B).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card B := Finset.card_univ
  have hB : Fintype.card B =
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) -
        Fintype.card
          (LPReplicaAggregateLowOrResolvableHighSourceRankFive
            G sites q) := by
    rw [Fintype.card_subtype]
    change (Finset.univ.filter fun y :
        LPReplicaAggregateDecoratedTarget G sites q => y ∉ used).card = _
    have hfilter : (Finset.univ.filter fun y :
        LPReplicaAggregateDecoratedTarget G sites q => y ∉ used) =
        Finset.univ \ used := by
      ext y
      simp
    rw [hfilter, Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr (Finset.subset_univ used),
      Finset.card_univ,
      card_lpReplicaAggregateRankFiveHandledTargetImage
        G sites hsite q hcard]
  unfold LPReplicaAggregateRankFiveResidualCapacity
  change Fintype.card A <= _
  rw [← hB]
  exact hAB


end
end StatMech.Ising
