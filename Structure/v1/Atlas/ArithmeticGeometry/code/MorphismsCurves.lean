/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/MorphismsCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


noncomputable section

open Module AlgebraicGeometry

universe u

namespace ArithmeticGeometry

/-- A curve over a field $k$: an integral scheme equipped with a smooth proper structure morphism to $\mathrm{Spec}(k)$ of relative dimension $1$. -/
structure Curve_k (k : Type u) [Field k] where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ Spec (.of k)
  [isIntegral : IsIntegral toScheme]
  [isProper : IsProper structureMorphism]
  [isSmooth : SmoothOfRelativeDimension 1 structureMorphism]

end ArithmeticGeometry
end
