/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohTildeFunctor


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace QCohMathlib

variable {R : CommRingCat.{u}}

/-- The tilde functor `Mod R → (Spec R).Modules` is faithful. -/
instance tilde_functor_faithful : (tilde.functor R).Faithful :=
  tilde.fullyFaithfulFunctor.faithful

/-- The tilde functor `Mod R → (Spec R).Modules` is full. -/
instance tilde_functor_full : (tilde.functor R).Full :=
  tilde.fullyFaithfulFunctor.full

end QCohMathlib
end
