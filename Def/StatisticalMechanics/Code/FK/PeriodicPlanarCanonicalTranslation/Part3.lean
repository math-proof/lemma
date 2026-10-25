/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part2
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]

noncomputable def PeriodicGraph.shiftBufferedEquiv
    (P : PeriodicGraph V) (z : Site 2) (n : Nat) :
    P.BufferedVertex n ≃ P.ShiftedBufferedVertex z n where
  toFun x := ⟨P.shift z x.1, Finset.mem_image.2 ⟨x.1, x.2, rfl⟩⟩
  invFun x := ⟨P.shift (-z) x.1, by
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 x.2
    rw [← hxy, P.shift_neg_shift]
    exact hy⟩
  left_inv x := Subtype.ext (P.shift_neg_shift z x.1)
  right_inv x := Subtype.ext (P.shift_shift_neg z x.1)

end StatMech.FK.PeriodicPlanar
