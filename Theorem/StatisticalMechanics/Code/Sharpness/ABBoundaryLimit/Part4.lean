/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.ABLatticeUnconditional
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryLimit.Part3
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

@[simp] theorem abblBoxEquiv_val (d n : Nat) (x : sctBox d n) :
    ((abblBoxEquiv d n x : ↑(ablBoxFinset d n)) : Site d) = x := rfl

@[simp] theorem abblBoxEquiv_origin (d n : Nat) :
    abblBoxEquiv d n (sctBoxOrigin d n) =
      ⟨(0 : Site d), zero_mem_ablBoxFinset d n⟩ := by
  ext i
  rfl


theorem abbl_abfaMag_eq_window (d n : Nat) (beta h : Real) :
    abfaMag (sctBoxGraph d n) (abbCoupling d n)
        (sctBoxOrigin d n) beta h =
      abfaMag
        (abigWindowGraph (hypercubicLattice d) (ablBoxFinset d n))
        (abigWindowCoupling (abblLatticeCoupling d) (ablBoxFinset d n))
        ⟨(0 : Site d), zero_mem_ablBoxFinset d n⟩ beta h := by
  simpa using abbl_abfaMag_relabel
    (sctBoxGraph d n)
    (abigWindowGraph (hypercubicLattice d) (ablBoxFinset d n))
    (abblBoxEquiv d n)
    (by
      intro x y
      simp [sctBoxGraph, abigWindowGraph, abblBoxEquiv])
    (abbCoupling d n)
    (abigWindowCoupling (abblLatticeCoupling d) (ablBoxFinset d n))
    (by
      intro x y hxy
      have hamb : (hypercubicLattice d).Adj (x : Site d) (y : Site d) := by
        simpa [sctBoxGraph] using hxy
      rw [abigWindowCoupling_mk, abblLatticeCoupling_mk]
      change 1 = if (hypercubicLattice d).Adj (x : Site d) (y : Site d)
        then 1 else 0
      rw [if_pos hamb])
    (sctBoxOrigin d n) beta h


theorem abbl_finiteGhost_eq_ambient {d n : Nat} (beta h : Real)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    abfaMag (sctBoxGraph d n) (abbCoupling d n)
        (sctBoxOrigin d n) beta h =
      (abigMeasure (abblLatticeCoupling d) beta h).real
        (connEvent (withGhost (hypercubicLattice d))
          (abigGhostWindow (ablBoxFinset d n) : Set (Option (Site d)))
          (some (origin d)) {none}) := by
  rw [abbl_abfaMag_eq_window]
  exact abig_abfaMag_eq_finiteConn (hypercubicLattice d)
    (abblLatticeCoupling d) (ablBoxFinset d n)
    ⟨origin d, zero_mem_ablBoxFinset d n⟩ beta h hbeta hh
    (abblLatticeCoupling_nonneg d) abblLatticeCoupling_support


theorem abbl_tendsto_finiteGhost_shiftedBase (d : Nat) (beta h : Real)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    Tendsto
      (fun n ↦ abfaMag (sctBoxGraph d n) (abbCoupling d n)
        (sctBoxOrigin d n) beta h)
      atTop
      (nhds (abigMag (hypercubicLattice d) (abblLatticeCoupling d)
        (0 : Site d) beta h)) := by
  have hlim := abig_tendsto_abfaMag_exhaustion
    (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
    beta h hbeta hh
    (abblLatticeCoupling_nonneg d) abblLatticeCoupling_support
    (ablBoxFinset d) (zero_mem_ablBoxFinset d)
    (ablGhostWindow_mono d) (ablGhostWindow_cover d)
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun n ↦
    (abbl_abfaMag_eq_window d n beta h).symm


theorem abbl_tendsto_boundaryError_zero (h : Real) (hh : 0 < h) :
    Tendsto
      (fun n : Nat ↦ Real.exp (-(h * (((n + 2 : Nat) : Real)))))
      atTop (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_neg_atBot_iff.mpr
  have hn : Tendsto (fun n : Nat ↦ ((n : Real) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hn.const_mul_atTop hh


theorem abbl_tendsto_abbMag_shifted (d : Nat) (beta h : Real)
    (hbeta : 0 ≤ beta) (hh : 0 < h) :
    Tendsto (fun n ↦ abbMag d (n + 1) beta h) atTop
      (nhds (abigMag (hypercubicLattice d) (abblLatticeCoupling d)
        (0 : Site d) beta h)) := by
  let M := abigMag (hypercubicLattice d) (abblLatticeCoupling d)
    (0 : Site d) beta h
  let P : Nat → Real := fun n ↦
    abfaMag (sctBoxGraph d (n + 1)) (abbCoupling d (n + 1))
      (sctBoxOrigin d (n + 1)) beta h
  let E : Nat → Real := fun n ↦
    Real.exp (-(h * (((n + 2 : Nat) : Real))))
  have hshift : Tendsto (fun n : Nat ↦ n + 1) atTop atTop :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 tendsto_id
  have hP : Tendsto P atTop (nhds M) := by
    exact (abbl_tendsto_finiteGhost_shiftedBase d beta h hbeta hh.le).comp hshift
  have hE : Tendsto E atTop (nhds 0) :=
    abbl_tendsto_boundaryError_zero h hh
  have hPE : Tendsto (fun n ↦ P n + E n) atTop (nhds M) := by
    simpa [M] using hP.add hE
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hP hPE
  · intro n
    simpa [P] using
      (abbl_abfaMag_le_abbMag_le (d := d) (n := n + 1)
        (Nat.succ_pos n) beta h hbeta hh.le).1
  · intro n
    simpa [P, E, Nat.add_assoc] using
      (abbl_abfaMag_le_abbMag_le (d := d) (n := n + 1)
        (Nat.succ_pos n) beta h hbeta hh.le).2


end Sharpness
end StatMech
