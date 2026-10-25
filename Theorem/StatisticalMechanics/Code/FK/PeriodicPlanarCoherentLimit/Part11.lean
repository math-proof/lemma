/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part11
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


theorem PeriodicGraph.wiredBufferedInfiniteVolume_isLimit
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.wiredBufferedMeasure (phi n) hp hp1 hq)
        (P.wiredBufferedInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (prokhorov_seq_compact
      (fun n => P.wiredBufferedMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩


theorem PeriodicGraph.freeBufferedMeasure_tendsto_cylinder
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    Tendsto
      (fun m => (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S)) atTop
      (nhds ((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S))) := by
  set f := fun m => (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) with hf
  have hmono : Monotone (fun k => f (N + k)) := by
    apply monotone_nat_of_le_succ
    intro k
    simpa [f, Nat.add_assoc] using
      P.freeBufferedMeasure_step_cylinder (Nat.le_add_right N k) hp hp1 hq hS
  have hbdd : BddAbove (Set.range fun k => f (N + k)) :=
    ⟨1, by rintro x ⟨k, rfl⟩; exact measureReal_le_one⟩
  set L := ⨆ k, f (N + k) with hL
  have hshift : Tendsto (fun k => f (N + k)) atTop (nhds L) := by
    rw [hL]
    exact tendsto_atTop_ciSup hmono hbdd
  have hfull : Tendsto f atTop (nhds L) := by
    have hk : Tendsto (fun k => f (k + N)) atTop (nhds L) := by
      simpa [Nat.add_comm] using hshift
    exact (Filter.tendsto_add_atTop_iff_nat N).mp hk
  obtain ⟨phi, hphi, hconv⟩ :=
    P.freeBufferedInfiniteVolume_isLimit hp hp1 (zero_lt_one.trans_le hq)
  have hport := hconv.tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hsub := hfull.comp hphi.tendsto_atTop
  have heq : L =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) :=
    tendsto_nhds_unique hsub hport
  rwa [heq] at hfull


theorem PeriodicGraph.wiredBufferedMeasure_tendsto_cylinder
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    Tendsto
      (fun m => (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S)) atTop
      (nhds ((P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S))) := by
  set f := fun m => (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) with hf
  have hanti : Antitone (fun k => f (N + k)) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa [f, Nat.add_assoc] using
      P.wiredBufferedMeasure_step_cylinder (Nat.le_add_right N k) hp hp1 hq hS
  have hbdd : BddBelow (Set.range fun k => f (N + k)) :=
    ⟨0, by rintro x ⟨k, rfl⟩; exact measureReal_nonneg⟩
  set L := ⨅ k, f (N + k) with hL
  have hshift : Tendsto (fun k => f (N + k)) atTop (nhds L) := by
    rw [hL]
    exact tendsto_atTop_ciInf hanti hbdd
  have hfull : Tendsto f atTop (nhds L) := by
    have hk : Tendsto (fun k => f (k + N)) atTop (nhds L) := by
      simpa [Nat.add_comm] using hshift
    exact (Filter.tendsto_add_atTop_iff_nat N).mp hk
  obtain ⟨phi, hphi, hconv⟩ :=
    P.wiredBufferedInfiniteVolume_isLimit hp hp1 (zero_lt_one.trans_le hq)
  have hport := hconv.tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hsub := hfull.comp hphi.tendsto_atTop
  have heq : L =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) :=
    tendsto_nhds_unique hsub hport
  rwa [heq] at hfull


theorem PeriodicGraph.freeBuffered_subseq_cylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.freeBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (N : ℕ) {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  have hport := hconv.tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hsub := (P.freeBufferedMeasure_tendsto_cylinder N hp hp1 hq hS).comp
    hphi.tendsto_atTop
  exact tendsto_nhds_unique hport hsub

theorem PeriodicGraph.wiredBuffered_subseq_cylinder_eq
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (nu : ProbabilityMeasure (ConfigSpace (Sym2 V)))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : WeakConvergesTo
      (fun n => P.wiredBufferedMeasure (phi n) hp hp1 (zero_lt_one.trans_le hq)) nu)
    (N : ℕ) {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (nu : Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) =
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  have hport := hconv.tendsto_real_of_isClopen
    (P.bufferedCylinder_isClopen N S)
  have hsub := (P.wiredBufferedMeasure_tendsto_cylinder N hp hp1 hq hS).comp
    hphi.tendsto_atTop
  exact tendsto_nhds_unique hport hsub


end PeriodicPlanar
end FK
end StatMech
