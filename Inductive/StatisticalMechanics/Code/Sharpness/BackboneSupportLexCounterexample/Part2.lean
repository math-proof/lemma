/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part2
open Finset


namespace StatMech.Sharpness

inductive shbK4Path03
  | p0123 | p013 | p0213 | p023 | p03
  deriving DecidableEq, Fintype


end StatMech.Sharpness
