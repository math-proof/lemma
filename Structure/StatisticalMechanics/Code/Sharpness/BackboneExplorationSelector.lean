/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

structure shb_DynamicEdgeExploration (D E : Type*) where
  edgeOrder : D → List E
  edgeOrder_nodup : ∀ D, (edgeOrder D).Nodup
  advance : D → E → D

end StatMech.Sharpness
