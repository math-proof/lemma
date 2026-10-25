/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneRectangleCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWQOneInfiniteVolume
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.FK

open StatMech.RSW.Box


def rq1_finiteRectangleEvent (N : ℕ) (a b c d : ℤ) :
    Set (ConfigSpace (Sym2 (boxVerts 2 N))) :=
  extendEdge 2 N ⁻¹' horizontalCrossingEvent a b c d


end Universality
end StatMech
