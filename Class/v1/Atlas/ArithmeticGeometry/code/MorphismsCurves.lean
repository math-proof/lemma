/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/MorphismsCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ArithmeticGeometry.code.MorphismsCurves


noncomputable section

open Module AlgebraicGeometry

universe u

namespace ArithmeticGeometry

attribute [instance] Curve_k.isIntegral Curve_k.isProper Curve_k.isSmooth

/-- A function field of one variable over $k$: a finitely generated extension $F/k$ of transcendence degree $1$ in which $k$ is algebraically closed in $F$. -/
class FunctionField_k (k : Type*) (F : Type*) [Field k] [Field F] [Algebra k F] where
  finitelyGenerated : (⊤ : IntermediateField k F).FG
  transcendenceDegreeOne : ∃ (x : F), Transcendental k x ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) F
  algClosedInF : ∀ (x : F), IsAlgebraic k x → x ∈ (⊥ : IntermediateField k F)


end ArithmeticGeometry
end
