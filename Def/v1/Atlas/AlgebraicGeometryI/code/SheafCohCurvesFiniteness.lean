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
import Structure.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness


namespace SheafCohCurvesFiniteness

open CohomologyP1 SheafCohomology


section TwoTermComplex

variable (k : Type*) [Field k]

attribute [instance] CechComplex2.inst0 CechComplex2.inst1
  CechComplex2.mod0 CechComplex2.mod1

/-- `H⁰` of a two-term Čech complex is the kernel of `d : C⁰ → C¹`. -/
def CechComplex2.H0 (C : CechComplex2 k) : Submodule k C.C0 :=
  LinearMap.ker C.d

end TwoTermComplex
end SheafCohCurvesFiniteness
