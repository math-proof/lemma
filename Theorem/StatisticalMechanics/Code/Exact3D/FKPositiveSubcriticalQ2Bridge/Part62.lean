/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part64
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha_map
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (a : (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).α) :
    (finiteBoundaryGhostCutoffDecrementIndex Ω).map
        (finiteBoundaryGhostCollapsedCutoffDecrementIndex_toCutoffAlpha Ω a) =
      ⟨((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a).1,
        ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a).2.toSourceData⟩ := by
  rfl


theorem
    finiteBoundaryGhostSelectedPairCutoffSum_eq_cutoffDecrementIndex_domain_indicator_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostSelectedPairCutoffSum β H n Ω =
      Finset.sum (finiteBoundaryGhostCutoffDecrementIndex Ω).domain
        (fun a =>
          (if Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM
                  (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)
                (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
                  (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)) =
              finiteBoundaryGhostOnePointSource 3 n then
              (1 : ℝ)
            else
              0) *
            Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
              (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
              (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
                a.2.1.1)) := by
  classical
  unfold finiteBoundaryGhostSelectedPairCutoffSum
    finiteBoundaryGhostCutoffDecrementIndex
  rw [Finset.sum_sigma]
  conv_lhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro v _hv
  rw [Finset.sum_sigma]
  conv_lhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  conv_lhs => rw [← Finset.sum_attach]

set_option maxHeartbeats 1000000 in


theorem
    finiteBoundaryGhostSelectedPairCutoffSum_le_collapsedCutoffDecrementIndex_domain_sum
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostSelectedPairCutoffSum β H n Ω ≤
      Finset.sum (finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).domain
        (fun a =>
          finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H
            ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a)) := by
  classical
  let I := finiteBoundaryGhostCutoffDecrementIndex Ω
  let Ic := finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω
  let P : I.α → Prop :=
    fun a => a.2.1.1 ∈ finiteBoundaryGhostOnePointSourceCutoff Ω
  let F : I.α → ℝ :=
    fun a =>
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)) =
          finiteBoundaryGhostOnePointSource 3 n then
          (1 : ℝ)
        else
          0) *
        Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n))
            a.2.1.1)
  let G : {a // P a} → ℝ :=
    fun a =>
      finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight β H
        ((finiteBoundaryGhostCollapsedCutoffDecrementIndex Ω).map a)
  have hselected :
      finiteBoundaryGhostSelectedPairCutoffSum β H n Ω =
        Finset.sum I.domain F := by
    simpa [I, F] using
      finiteBoundaryGhostSelectedPairCutoffSum_eq_cutoffDecrementIndex_domain_indicator_sum
        (β := β) (H := H) Ω
  rw [hselected]
  change Finset.sum I.domain F ≤ Finset.sum Ic.domain G
  change Finset.sum I.domain F ≤ Finset.sum (Finset.subtype P I.domain) G
  refine
    finset_sum_le_subtype_sum_of_inactive_nonpos
      I.domain P F G ?_ ?_
  · intro a _ha hnotP
    dsimp [F, P]
    have hsrc_ne :
        ¬ Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
              (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)) =
          finiteBoundaryGhostOnePointSource 3 n := by
      intro hsrc
      exact hnotP (Finset.mem_filter.mpr ⟨a.2.1.2, hsrc⟩)
    rw [if_neg hsrc_ne]
    simp
  · intro a _ha haP
    dsimp [F, G, P]
    have hsrc :
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) a.2.1.1)) =
          finiteBoundaryGhostOnePointSource 3 n :=
      (Finset.mem_filter.mp haP).2
    have hvbdry : FK.boxBoundary 3 n a.1.1 :=
      (Finset.mem_filter.mp a.1.2).2
    simpa [finiteBoundaryGhostCollapsedCutoffDecrementIndex,
      finiteBoundaryGhostSigmaCollapsedTwoPointSourceDataWeight,
      finiteBoundaryGhostCollapsedTwoPointSourceDataWeight,
      finiteBoundaryGhostTwoPointSourceDataWeight] using
      finiteBoundaryGhostBoundaryCrossingPairs_indicator_weight_le_collapsedDecrementDataWeight
        (β := β) (H := H) hβ hH a.2.1.1 hvbdry hsrc a.2.2.2


theorem finiteBoundaryGhostCutoffDecrementIndex_mem_domain
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) :
    a ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).domain := by
  classical
  rcases a with ⟨v, m, p⟩
  unfold finiteBoundaryGhostCutoffDecrementIndex
  exact Finset.mem_sigma.mpr
    ⟨Finset.mem_attach _ v,
      Finset.mem_sigma.mpr
        ⟨Finset.mem_attach _ m, Finset.mem_attach _ p⟩⟩

set_option maxHeartbeats 800000 in


theorem finiteBoundaryGhostCutoffDecrementIndex_domain_card_eq_crossingPairs_sum
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    ((finiteBoundaryGhostCutoffDecrementIndex Ω).domain.card : ℝ) =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ m ∈ Ω,
          ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ) := by
  classical
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  unfold finiteBoundaryGhostCutoffDecrementIndex
  dsimp only
  rw [Finset.card_sigma]
  simp only [Finset.card_sigma, Finset.card_attach, Nat.cast_sum]
  change
    (∑ x ∈ B.attach,
      ∑ x_1 ∈ Ω.attach,
        ((finiteBoundaryGhostBoundaryCrossingPairs x_1.1 x.1).card : ℝ)) =
      ∑ v ∈ B,
        ∑ m ∈ Ω,
          ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ)
  have hinner (v : FK.boxVerts 3 n) :
      (∑ x_1 ∈ Ω.attach,
        ((finiteBoundaryGhostBoundaryCrossingPairs x_1.1 v).card : ℝ)) =
        ∑ m ∈ Ω,
          ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ) := by
    exact
      Finset.sum_attach Ω
        (fun m => ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ))
  calc
    (∑ x ∈ B.attach,
      ∑ x_1 ∈ Ω.attach,
        ((finiteBoundaryGhostBoundaryCrossingPairs x_1.1 x.1).card : ℝ)) =
        ∑ x ∈ B.attach,
          ∑ m ∈ Ω,
            ((finiteBoundaryGhostBoundaryCrossingPairs m x.1).card : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro x _hx
      exact hinner x.1
    _ =
        ∑ v ∈ B,
          ∑ m ∈ Ω,
            ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ) := by
      exact
        Finset.sum_attach B
          (fun v =>
            ∑ m ∈ Ω,
              ((finiteBoundaryGhostBoundaryCrossingPairs m v).card : ℝ))


theorem finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_iff_map_eq
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v))
    (a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) :
    a ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d ↔
      (finiteBoundaryGhostCutoffDecrementIndex Ω).map a = d := by
  classical
  constructor
  · intro ha
    exact ((FinsetFiberIndex.mem_fiber
      (finiteBoundaryGhostCutoffDecrementIndex Ω) d a).mp ha).2
  · intro hmap
    exact ((FinsetFiberIndex.mem_fiber
      (finiteBoundaryGhostCutoffDecrementIndex Ω) d a).mpr
        ⟨finiteBoundaryGhostCutoffDecrementIndex_mem_domain Ω a, hmap⟩)

@[simp] theorem finiteBoundaryGhostCutoffDecrementIndex_map_fst
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α) :
    ((finiteBoundaryGhostCutoffDecrementIndex Ω).map a).1 = a.1.1 := by
  rfl


theorem finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_fst_eq
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {d : Sigma (fun v : FK.boxVerts 3 n =>
      finiteBoundaryGhostTwoPointSourceData n v)}
    {a : (finiteBoundaryGhostCutoffDecrementIndex Ω).α}
    (ha : a ∈ (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber d) :
    a.1.1 = d.1 := by
  have hmap :
      (finiteBoundaryGhostCutoffDecrementIndex Ω).map a = d :=
      (finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_iff_map_eq
      Ω d a).mp ha
  simpa using congrArg Sigma.fst hmap


theorem finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_heq
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {w : {w : FK.boxVerts 3 n //
      w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
    {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
      m ∈ Ω}}
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
    (ha : (⟨w, ⟨m, p⟩⟩ :
      (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈
      (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostTwoPointSourceData n v))) :
    HEq
      (finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := p.1) m.1 w.1 p.2) d := by
  have hmap :
      (finiteBoundaryGhostCutoffDecrementIndex Ω).map
        (⟨w, ⟨m, p⟩⟩ :
          (finiteBoundaryGhostCutoffDecrementIndex Ω).α) =
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostTwoPointSourceData n v)) :=
    (finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_iff_map_eq
      Ω (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
        finiteBoundaryGhostTwoPointSourceData n v))
      (⟨w, ⟨m, p⟩⟩ :
        (finiteBoundaryGhostCutoffDecrementIndex Ω).α)).mp ha
  have hmap' :
      (⟨w.1,
        finiteBoundaryGhostBoundaryCrossingPairDecrementData
          (p := p.1) m.1 w.1 p.2⟩ :
        Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostTwoPointSourceData n v)) =
        ⟨v, d⟩ := by
    simpa [finiteBoundaryGhostCutoffDecrementIndex] using hmap
  exact (Sigma.mk.inj_iff.mp hmap').2


theorem finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_eq
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {w : {w : FK.boxVerts 3 n //
      w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
    {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
      m ∈ Ω}}
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
    (ha : (⟨w, ⟨m, p⟩⟩ :
      (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈
      (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostTwoPointSourceData n v)))
    (hvw : w.1 = v) :
    finiteBoundaryGhostBoundaryCrossingPairDecrementData
        (p := p.1) m.1 w.1 p.2 =
      (hvw.symm ▸ d) := by
  subst v
  exact eq_of_heq
    (finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_heq
      Ω d ha)


theorem finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_exists_localFiber
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (d : finiteBoundaryGhostTwoPointSourceData n v)
    {w : {w : FK.boxVerts 3 n //
      w ∈ Finset.univ.filter (FK.boxBoundary 3 n)}}
    {m : {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ //
      m ∈ Ω}}
    {p : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 w.1}}
    (ha : (⟨w, ⟨m, p⟩⟩ :
      (finiteBoundaryGhostCutoffDecrementIndex Ω).α) ∈
      (finiteBoundaryGhostCutoffDecrementIndex Ω).fiber
        (⟨v, d⟩ : Sigma (fun v : FK.boxVerts 3 n =>
          finiteBoundaryGhostTwoPointSourceData n v))) :
    ∃ p' : {p // p ∈ finiteBoundaryGhostBoundaryCrossingPairs m.1 v},
      p'.1 = p.1 ∧
      p' ∈ finiteBoundaryGhostBoundaryCrossingPairDecrementFiber
        m.1 v d := by
  have hvw : w.1 = v :=
    finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_fst_eq
      Ω (a := (⟨w, ⟨m, p⟩⟩ :
        (finiteBoundaryGhostCutoffDecrementIndex Ω).α)) ha
  subst v
  refine ⟨p, rfl, ?_⟩
  exact (finiteBoundaryGhostBoundaryCrossingPairDecrementFiber_mem
    m.1 w.1 d p).mpr
    (finiteBoundaryGhostCutoffDecrementIndex_mem_fiber_decrementData_eq
      Ω d ha rfl)


end Exact3D
end StatMech
