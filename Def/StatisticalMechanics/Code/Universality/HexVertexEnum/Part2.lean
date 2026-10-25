/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexEnum.Part2


namespace StatMech.Universality

open Complex

open HexWalk


noncomputable def combinedSummand (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ) : ℂ :=
  ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts
    + ((v + hexOmega * du) - v)
        * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts
    + ((v + hexOmega ^ 2 * du) - v)
        * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts


end StatMech.Universality
