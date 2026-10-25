/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part4


namespace StatMech.Universality

open Complex

open scoped BigOperators


def hexSplitAt (cp : List ℤ → ℕ) (ts : List ℤ) : (List ℤ × ℕ) × (List ℤ × ℕ) :=
  ((ts.take (cp ts), cp ts), (ts.drop (cp ts), cp ts))


end StatMech.Universality
