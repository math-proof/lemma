/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Def.StatisticalMechanics.Code.Lattice.EarContraction.Part6
open SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem transSub_val (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) : (transSub K w a).1 = transDart w a.1 := rfl


theorem isPeriodicPt_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    Function.IsPeriodicPt (dartNextSub (transSet w K)) n (transSub K w a) ↔
      Function.IsPeriodicPt (dartNextSub K) n a := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    show ((dartNextSub K)^[n] a).1 = a.1
    rw [dartNextSub_iterate_val]
    have hstep : (dartNext (transSet w K))^[n] (transSub K w a).1 =
        transDart w ((dartNext K)^[n] a.1) := by
      show (dartNext (transSet w K))^[n] (transDart w a.1) = _
      rw [iterate_dartNext_trans]
    rw [hstep] at hv
    exact transDart_injective w hv
  · intro h
    apply Subtype.ext
    rw [dartNextSub_iterate_val]
    show (dartNext (transSet w K))^[n] (transDart w a.1) = transDart w a.1
    rw [iterate_dartNext_trans]
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    rw [hv]


theorem dartOrbitPeriod_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod (transSet w K) (transSub K w a) = dartOrbitPeriod K a := by
  unfold dartOrbitPeriod
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  exact isPeriodicPt_trans K w a n


theorem cornerBalance_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance (transSet w K) (transSub K w a) = cornerBalance K a := by
  unfold cornerBalance
  rw [transSub_val, dartOrbitPeriod_trans, rightCornerCount_trans, leftCornerCount_trans]


end Lattice
end StatMech
