/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModuleDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Mathlib.Algebra.Lie.Semisimple.Defs
import Def.v1.Atlas.LieGroups.code.GKModuleDefs


noncomputable section

open scoped ComplexOrder

structure SemisimpleLieGroup where
  G : Type*
  instGroup : Group G
  instTopologicalSpace : TopologicalSpace G
  instIsTopologicalGroup : IsTopologicalGroup G
  𝔤 : Type*
  instLieRing : LieRing 𝔤
  instLieAlgebra : LieAlgebra ℝ 𝔤
  isSemisimple : LieAlgebra.IsSemisimple ℝ 𝔤
  lieExp : 𝔤 → G
  lieExp_zero : lieExp 0 = @One.one G instGroup.toOne


end
