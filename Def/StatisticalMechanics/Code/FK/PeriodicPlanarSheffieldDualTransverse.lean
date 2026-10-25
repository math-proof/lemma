/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


noncomputable def PeriodicPlaneEmbedding.orbitBoxCoordinateBound
    (E : PeriodicPlaneEmbedding P) (n : Nat) (i : Fin 2) : Real :=
  (P.orbitBox n).sup'
    ⟨P.root, P.orbitBox_mono (Nat.zero_le n) P.root_mem_orbitBox_zero⟩
    (fun v => |E.vertexCoord v i|)

end StatMech.FK.PeriodicPlanar
