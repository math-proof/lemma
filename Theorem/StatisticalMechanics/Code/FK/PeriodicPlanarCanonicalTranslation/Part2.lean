/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part4
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

theorem PeriodicGraph.freeBufferedMeasure_real_multiOpen
    (P : PeriodicGraph V) (n : Nat)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (t : Finset (Sym2 (P.BufferedVertex n))) :
    (P.freeBufferedMeasure n hp hp1 hq : Measure (ConfigSpace (Sym2 V))).real
        (fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius n)))) =
      med_multiMassProb (fkProb (P.bufferedGraph n) p q) t := by
  classical
  have hevent : fmu_multiOpen (t.image (P.edgeIncl (P.bufferedRadius n))) =
      P.bufferedCylinder n (med_genericMultiOpenEvent t) := by
    ext omega
    simp only [fmu_multiOpen, Set.mem_setOf_eq, Finset.forall_mem_image,
      PeriodicGraph.bufferedCylinder, Set.mem_preimage,
      med_genericMultiOpenEvent, PeriodicGraph.bufferedRestrict]
  rw [hevent, P.freeBufferedMeasure_real_cylinder (le_refl n) hp hp1 hq]
  unfold med_multiMassProb
  apply Finset.sum_congr rfl
  intro omega _
  have hrefl : P.bufferedRestrictLE (le_refl n) omega = omega := by
    funext e
    induction e using Sym2.inductionOn with
    | _ x y => rfl
  unfold Set.indicator
  change (if P.bufferedRestrictLE (le_refl n) omega ∈
      med_genericMultiOpenEvent t then 1 else 0) * _ = _
  rw [hrefl]

theorem PeriodicGraph.centered_eq_shifted_free_multiMass
    (P : PeriodicGraph V) (z : Site 2) (n : Nat)
    (t : Finset (Sym2 (P.BufferedVertex n))) (p q : Real) :
    med_multiMassProb (fkProb (P.bufferedGraph n) p q) t =
      med_multiMassProb (fkProb (P.shiftedBufferedGraph z n) p q)
        (t.image (Sym2.map (P.shiftBufferedEquiv z n))) := by
  unfold med_multiMassProb
  rw [← cdc_eventMassProb_reCfgIso_inv (P.shiftBufferedEquiv z n)
    (fkProb (P.bufferedGraph n) p q)
    (fkProb (P.shiftedBufferedGraph z n) p q)
    (fun omega => fvs_fkProb_reCfgIso (P.bufferedGraph n)
      (P.shiftedBufferedGraph z n) (P.shiftBufferedEquiv z n)
      (P.shiftBufferedEquiv_adj z n) p q omega)
    (med_genericMultiOpenEvent t)]
  refine Finset.sum_congr rfl fun omega _ => ?_
  rw [med_reCfgIso_preimage (P.shiftBufferedEquiv z n) t]

theorem PeriodicGraph.shifted_free_multiMass_le_buffered
    (P : PeriodicGraph V) (z : Site 2) (n m : Nat)
    (hsub : (P.shiftedBufferedVertices z n : Set V) ⊆
      (P.orbitBox (P.bufferedRadius m) : Set V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (Sym2 (P.ShiftedBufferedVertex z n))) :
    med_multiMassProb (fkProb (P.shiftedBufferedGraph z n) p q) t ≤
      med_multiMassProb (fkProb (P.bufferedGraph m) p q)
        (t.image (ocd_innerEdge (P.shiftedToBufferedIncl z n m hsub))) := by
  let incl := P.shiftedToBufferedIncl z n m hsub
  have hinj : Function.Injective incl := fun x y h =>
    Subtype.ext (congrArg (fun v : P.BufferedVertex m => v.1) h)
  have hadj : ocd_AdjMatch (P.shiftedBufferedGraph z n)
      (P.bufferedGraph m) incl := by
    intro x y
    rfl
  have hdom := bdp_free_inner_dominated_fkProb hinj hadj hp hp1 hq
    (A := med_genericMultiOpenEvent t) (med_genericMultiOpenEvent_increasing t)
  rw [ocd_innerRestrict_preimage_multiOpenEvent hinj t] at hdom
  exact hdom

theorem PeriodicGraph.buffered_free_multiMass_le_shifted
    (P : PeriodicGraph V) (z : Site 2) (n m : Nat)
    (hsub : (P.orbitBox (P.bufferedRadius n) : Set V) ⊆
      (P.shiftedBufferedVertices z m : Set V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (Sym2 (P.BufferedVertex n))) :
    med_multiMassProb (fkProb (P.bufferedGraph n) p q) t ≤
      med_multiMassProb (fkProb (P.shiftedBufferedGraph z m) p q)
        (t.image (ocd_innerEdge (P.bufferedToShiftedIncl z n m hsub))) := by
  let incl := P.bufferedToShiftedIncl z n m hsub
  have hinj : Function.Injective incl := fun x y h =>
    Subtype.ext (congrArg (fun v : P.ShiftedBufferedVertex z m => v.1) h)
  have hadj : ocd_AdjMatch (P.bufferedGraph n)
      (P.shiftedBufferedGraph z m) incl := by
    intro x y
    rfl
  have hdom := bdp_free_inner_dominated_fkProb hinj hadj hp hp1 hq
    (A := med_genericMultiOpenEvent t) (med_genericMultiOpenEvent_increasing t)
  rw [ocd_innerRestrict_preimage_multiOpenEvent hinj t] at hdom
  exact hdom

end StatMech.FK.PeriodicPlanar
