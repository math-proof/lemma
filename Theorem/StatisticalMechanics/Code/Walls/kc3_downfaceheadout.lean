/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc3_dartFace_down_eq_head (e : Dart) (hd : e.dir = ![0, -1]) :
    dartFace e = e.head := by
  rw [dartFace_of_dir_down e hd, dart_head_eq e, hd]
  funext i
  fin_cases i
  · simp
  · simp; ring


theorem kc3_down_head_notMem {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (_hd : e.dir = ![0, -1]) :
    e.head ∉ K :=
  he.head_not_mem


theorem kc3_dartFace_down_notMem {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) :
    dartFace e ∉ K := by
  rw [kc3_dartFace_down_eq_head e hd]
  exact kc3_down_head_notMem he hd


theorem kc3_down_zInK_unattainable {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) :
    ¬ (dartFace e ∈ K) :=
  kc3_dartFace_down_notMem he hd


theorem kc3_down_zInK_false {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) (hmem : dartFace e ∈ K) :
    False :=
  kc3_down_zInK_unattainable he hd hmem


theorem kc3_down_supportOdd_forces_even (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![0, -1]) (hsupp : dartFace e ∈ (mpl_orbitLoop K a).support)
    (hres : exc_SupportOddInK K a) :
    Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) := by
  by_contra hodd
  exact kc3_down_zInK_unattainable he hd (hres (dartFace e) hsupp hodd)


end Walls
end StatMech
