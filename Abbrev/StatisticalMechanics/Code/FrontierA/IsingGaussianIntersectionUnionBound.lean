/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianIntersectionUnionBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourCurrentTree
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev TreeFourProfiles (G : SimpleGraph V) [DecidableRel G.Adj] :=
  ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) ×
    ((G.edgeFinset -> Nat) × (G.edgeFinset -> Nat))


end StatMech.FrontierA
