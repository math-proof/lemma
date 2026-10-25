/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohTildeFunctor
import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohMathlib


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace QCohMathlib

variable {R : CommRingCat.{u}}

/-- Packaged fully-faithful structure for the tilde functor, exposing both
fullness and faithfulness simultaneously. -/
def tilde_fullyFaithful : (tilde.functor R).FullyFaithful :=
  tilde.fullyFaithfulFunctor

end QCohMathlib
end
