/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneEscape.Part2
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.setConnectionWithin_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A S T : Set V) :
    P.configTranslate z omega ∈
        P.setConnectionWithin (P.shift z '' A)
          (P.shift z '' S) (P.shift z '' T) ↔
      omega ∈ P.setConnectionWithin A S T := by
  constructor
  · rintro ⟨xz, ⟨x, hx, rfl⟩, yz, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨x, hx, y, hy,
      (P.connectedWithinSet_configTranslate z omega A x y).mp hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨P.shift z x, ⟨x, hx, rfl⟩,
      P.shift z y, ⟨y, hy, rfl⟩,
      (P.connectedWithinSet_configTranslate z omega A x y).mpr hxy⟩

theorem PeriodicGraph.setConnectionWithin_mono_target
    (P : PeriodicGraph V) (A S : Set V) {T U : Set V} (hTU : T ⊆ U) :
    P.setConnectionWithin A S T ⊆ P.setConnectionWithin A S U := by
  rintro omega ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hTU hy, hxy⟩


end StatMech.FK.PeriodicPlanar
