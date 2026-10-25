/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction
import Structure.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary


namespace StatMech.Universality

open Complex Set

open scoped BigOperators


namespace HexMirrorBoundaryPair

variable {V : Type*} [DecidableEq V]

variable {D : HexDomain V} {heading : V → Fin 3 → ℤ}


noncomputable def piece (Q : HexMirrorBoundaryPair D heading) :
    Finset (HexIncidence V) :=
  Q.neg ∪ Q.pos


end HexMirrorBoundaryPair
end StatMech.Universality
