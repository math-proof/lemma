/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexPairedBoundaryNormalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame


namespace StatMech.Universality

open scoped BigOperators


inductive HexPairedBoundaryClass
  | side
  | slant
  | top
  deriving DecidableEq

end StatMech.Universality
