/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
open Finset


namespace StatMech.Sharpness

inductive shbK4Edge
  | e01 | e02 | e03 | e12 | e13 | e23
  deriving DecidableEq, Fintype

end StatMech.Sharpness
