/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexSeparation.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexVertexCoverage
import Structure.StatisticalMechanics.Code.Universality.HexVertexClassification


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


namespace HexSawClassification

variable (C : HexSawClassification region a h0 v du)


def toEnum : HexVertexEnumeration region a h0 v du where
  pairs := C.pairs
  pairBase := C.pairBase
  pairLq := C.pairLq
  pairLr := C.pairLr
  pairLq_sum := C.pairLq_sum
  pairLr_sum := C.pairLr_sum
  pairLen := C.pairLen
  pairQ_valid := C.pairQ_valid
  pairR_valid := C.pairR_valid
  triplets := C.triplets
  tripBase := C.tripBase
  tripP_valid := C.tripP_valid
  tripQ_valid := C.tripQ_valid
  tripR_valid := C.tripR_valid
  reindex := C.reindex

end HexSawClassification
end StatMech.Universality
