/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem ons_weightedRootIdentity_unconditional
    (L : Nat) [Fact (2 < L)] :
    ons_weightedRootIdentity L := by
  apply ons_weightedRootIdentity_of_decoratedFormal L
  apply ons_decoratedFormalKacWardIdentity_of_repeatedEdge_vanishes L
  intro a b m edge hrepeated
  exact ons_decFormalRoot_coeff_eq_zero_of_repeated
    L a b m edge hrepeated


end StatMech.FrontierA
