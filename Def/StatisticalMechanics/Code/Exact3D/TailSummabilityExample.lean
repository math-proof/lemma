/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilityExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummabilityExample

noncomputable def exampleSplit : ContributionSplit (Fin 2) where
  finiteContribution := fun _ => (1 : ℝ)
  tailContribution := fun _ => (1 : ℝ) / 10
  totalContribution := fun _ => (11 : ℝ) / 10


def exampleTable : RatInterval.CaseTable Unit where
  cases := Finset.univ
  interval := fun _ => RatInterval.point 1


def exampleClassifier (_ : Fin 2) : Unit := ()


end TailSummabilityExample
end Exact3D
end StatMech
