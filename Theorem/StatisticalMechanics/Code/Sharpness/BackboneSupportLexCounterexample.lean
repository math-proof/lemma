/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Instance.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part3
open Finset


namespace StatMech.Sharpness

theorem shbK4_selectsDirect03_iff_pathEnumeration
    (A : Finset shbK4Edge) :
    shbK4SelectsDirect03 A ↔
      shbK4Boundary A = {0, 3} ∧
        shbK4SupportsPath A shbK4Path03.p03 ∧
        ∀ p, p ≠ shbK4Path03.p03 → ¬ shbK4SupportsPath A p := by
  decide +revert +kernel


end StatMech.Sharpness
