/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


noncomputable def hexFiniteStripPhysicalStartFiber
    {R : HexFiniteRegion} {D : HexDomain V} (P : D.InteriorPairing) :
    Finset (HexIncidence V) :=
  (D.incidences \ P.interior).filter
    (fun e => D.mid e.vtx e.edge = R.start)


end StatMech.Universality
