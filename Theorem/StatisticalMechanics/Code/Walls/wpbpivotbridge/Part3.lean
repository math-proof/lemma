/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wcddefectbridge.Part5
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Def.StatisticalMechanics.Code.Walls.wpbpivotbridge.Part2
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wpb

open StatMech.Lattice

open StatMech.Wad

open StatMech.Wcd

open StatMech.Walls

open StatMech.Euc


theorem wpb_covering_of_orbitCovers (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (hcov : WpbOrbitCovers K a) :
    ∀ v ∈ regVerts (wcd_toVtxFinset K hK),
      v ∉ (Finset.range (dartOrbitPeriod K a)).image
        (fun i => wcd_pivot ((dartNext K)^[i] a.1)) →
      defect (wcd_toVtxFinset K hK) v = 0 := by
  classical
  intro v hv hvimg
  obtain ⟨x, y⟩ := v
  refine wpb_defect_zero_of_no_boundary_pivot K hK x y hv ?_
  intro e he hpe
  obtain ⟨n, hn⟩ := hcov e he
  have hpos := dartOrbitPeriod_pos K hK a
  have hmod : (dartNextSub K)^[n % dartOrbitPeriod K a] a = (dartNextSub K)^[n] a :=
    Function.iterate_mod_minimalPeriod_eq (f := dartNextSub K) (x := a) (n := n)
  have hval : (dartNext K)^[n % dartOrbitPeriod K a] a.1 = (dartNext K)^[n] a.1 := by
    have h := congrArg Subtype.val hmod
    rwa [dartNextSub_iterate_val, dartNextSub_iterate_val] at h
  apply hvimg
  rw [Finset.mem_image]
  refine ⟨n % dartOrbitPeriod K a, Finset.mem_range.mpr (Nat.mod_lt _ hpos), ?_⟩
  show wcd_pivot ((dartNext K)^[n % dartOrbitPeriod K a] a.1) = (x, y)
  rw [hval, hn, hpe]


theorem wpb_pivotBridge_of (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) (hcov : WpbOrbitCovers K a) :
    WcdPivotBridge K hK a :=
  ⟨hpf, wpb_pivotInjective K a hpf, wpb_covering_of_orbitCovers K hK a hcov⟩


theorem wpb_revCount_pm_one (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) (hcov : WpbOrbitCovers K a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wcd_revCount_pm_one K hK a (wpb_pivotBridge_of K hK a hpf hcov) hbuild


theorem wpb_balanceIsFour (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a) (hcov : WpbOrbitCovers K a)
    (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
    BalanceIsFour K a :=
  wcd_balanceIsFour K hK a (wpb_pivotBridge_of K hK a hpf hcov) hbuild


theorem wpb_frontCell_notMem_unitCell (e : Dart) (he : IsBoundaryDart unitCell e) :
    wcd_frontCell e ∉ unitCell := by
  intro hf
  have htail : e.tail = ![0, 0] := by
    have h := he.1; rwa [unitCell, Set.mem_singleton_iff] at h
  rw [unitCell, Set.mem_singleton_iff, wcd_frontCell] at hf
  have hhe : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  rw [hhe, htail] at hf
  apply dartDir_ne_zero e
  have h0 := congrFun hf 0
  have h1 := congrFun hf 1
  simp only [rot90Fun, Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h0 h1
  have hz0 : e.dir 0 = 0 := by omega
  have hz1 : e.dir 1 = 0 := by omega
  funext i; fin_cases i
  · exact hz0
  · exact hz1


theorem wpb_witness_pinchFree_unitCell : WpbPinchFree unitCell ucBase := by
  intro i _ hconj
  exact wpb_frontCell_notMem_unitCell _
    (iterate_isBoundaryDart unitCell ucBase.1 ucBase.2 i) hconj.1


theorem wpb_witness_orbitCovers_unitCell : WpbOrbitCovers unitCell ucBase := by
  intro d hd
  exact ifc_singleton_sameOrbit (![0, 0] : Site 2) ucBase.1 d ucBase.2 hd


theorem wpb_witness_pivotBridge_unitCell :
    WcdPivotBridge unitCell wcd_unitCell_finite ucBase :=
  wpb_pivotBridge_of unitCell wcd_unitCell_finite ucBase
    wpb_witness_pinchFree_unitCell wpb_witness_orbitCovers_unitCell


theorem wpb_witness_revCount_unitCell : revCount unitCell ucBase = -1 := by
  have hbuild : EucBuildable (wcd_toVtxFinset unitCell wcd_unitCell_finite) := by
    rw [wcd_toVtxFinset_unitCell wcd_unitCell_finite]
    exact EucBuildable.singleton ((0 : ℤ), (0 : ℤ))
  exact wcd_revCount_eq_neg_one unitCell wcd_unitCell_finite ucBase
    wpb_witness_pivotBridge_unitCell hbuild

end Wpb
end StatMech
