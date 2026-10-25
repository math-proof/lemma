/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexColumnMembershipClose


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


def hcm_SpansWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) : Prop :=
  ∃ u ∈ (HexWalk.ofTurns a h0 ts).vertices, ∃ w ∈ (HexWalk.ofTurns a h0 ts).vertices,
    (T : ℝ) ≤ w.re - u.re


end StatMech.Universality
