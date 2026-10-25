/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.DartOrbit.Part5
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem dartOrbitWalk_length (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).length = dartOrbitPeriod K a := by
  unfold dartOrbitWalk
  rw [SimpleGraph.Walk.length_copy, orbitWalkAux_length]


theorem dartOrbitWalk_length_pos (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 0 < (dartOrbitWalk K a).length := by
  rw [dartOrbitWalk_length]; exact dartOrbitPeriod_pos K hK a


theorem dartOrbitWalk_ne_nil (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : dartOrbitWalk K a ≠ SimpleGraph.Walk.nil := by
  intro h
  have := dartOrbitWalk_length_pos K hK a
  rw [h] at this
  simp at this


theorem dartOrbitWalk_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).support
      = (List.range (dartOrbitPeriod K a + 1)).map (fun k => (dartNextSub K)^[k] a) := by
  unfold dartOrbitWalk
  rw [SimpleGraph.Walk.support_copy, orbitWalkAux_support]


theorem iterate_inj_on_Icc_minimalPeriod {α : Type*} (f : α → α) (x : α) {j k : ℕ}
    (hpos : 0 < Function.minimalPeriod f x)
    (hj1 : 1 ≤ j) (hjp : j ≤ Function.minimalPeriod f x)
    (hk1 : 1 ≤ k) (hkp : k ≤ Function.minimalPeriod f x)
    (h : f^[j] x = f^[k] x) : j = k := by
  set p := Function.minimalPeriod f x with hp
  have hjk : f^[j % p] x = f^[k % p] x := by
    rw [Function.iterate_mod_minimalPeriod_eq, Function.iterate_mod_minimalPeriod_eq, h]
  have hjlt : j % p < p := Nat.mod_lt _ hpos
  have hklt : k % p < p := Nat.mod_lt _ hpos
  have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := x)
    (Set.mem_Iio.mpr hjlt) (Set.mem_Iio.mpr hklt) hjk
  have hj : j % p = if j = p then 0 else j := by
    rcases eq_or_lt_of_le hjp with h' | h'
    · simp [h', Nat.mod_self]
    · rw [if_neg (by omega), Nat.mod_eq_of_lt h']
  have hk : k % p = if k = p then 0 else k := by
    rcases eq_or_lt_of_le hkp with h' | h'
    · simp [h', Nat.mod_self]
    · rw [if_neg (by omega), Nat.mod_eq_of_lt h']
  rw [hj, hk] at hinj
  split_ifs at hinj <;> omega


theorem dartOrbitWalk_support_tail_nodup (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).support.tail.Nodup := by
  rw [dartOrbitWalk_support]
  have hpe : dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl
  set p := dartOrbitPeriod K a with hp
  have hpos : 0 < Function.minimalPeriod (dartNextSub K) a := dartOrbitPeriod_pos K hK a
  rw [List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
  apply List.Nodup.map_on (l := List.range p) (f := (fun k => (dartNextSub K)^[k] a) ∘ Nat.succ)
  · intro j hj k hk h
    simp only [List.mem_range] at hj hk
    simp only [Function.comp_apply] at h
    have := iterate_inj_on_Icc_minimalPeriod (dartNextSub K) a (j := j + 1) (k := k + 1)
      hpos (by omega) (by omega) (by omega) (by omega) h
    omega
  · exact List.nodup_range

end Lattice
end StatMech
