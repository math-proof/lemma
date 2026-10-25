/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part3


namespace StatMech.Universality

open List


def hexHW_leadRun (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (p :: rest).takeWhile (fun q => q.1 == p.1)


def hexHW_dropRun (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (p :: rest).dropWhile (fun q => q.1 == p.1)

end StatMech.Universality
