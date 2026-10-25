/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/WeaklyAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraFunctor
import Lemma.Set.Dense_KFiniteSubspace.of.IsAdmissible
import Lemma.Submodule.Any_And_All_Eq_GetToMonoidHomAndAll_In_Span.of.IsMaximalCompactSubgroup.IsSemisimpleLieGroupG
import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
import Def.v1.Atlas.LieGroups.code.AnalyticityRegularity.Part2
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Group.Quotient
import Def.v1.Atlas.LieGroups.code.WeaklyAnalytic
universe uFw


noncomputable section

set_option autoImplicit false

open scoped Manifold

open EllipticOperator in
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (h : IsEllipticAt f)
    (p : E) (hp : p ≠ 0) : f p ≠ 0 := h p hp

end
