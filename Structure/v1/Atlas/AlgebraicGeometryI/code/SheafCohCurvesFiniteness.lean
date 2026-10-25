/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohCurvesFiniteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2


namespace SheafCohCurvesFiniteness

open CohomologyP1 SheafCohomology


section TwoTermComplex

variable (k : Type*) [Field k]

/-- A two-term Čech complex `C⁰ → C¹` over a field `k`: the natural model
for the Čech cohomology of a sheaf on a two-element open cover. -/
structure CechComplex2 (k : Type*) [Field k] where
  C0 : Type*
  C1 : Type*
  [inst0 : AddCommGroup C0]
  [inst1 : AddCommGroup C1]
  [mod0 : Module k C0]
  [mod1 : Module k C1]
  d : C0 →ₗ[k] C1

end TwoTermComplex
end SheafCohCurvesFiniteness
