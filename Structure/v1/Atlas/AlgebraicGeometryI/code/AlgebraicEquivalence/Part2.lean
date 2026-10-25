/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AlgebraicEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Connected.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.AlgebraicEquivalence.Part3


noncomputable section

namespace AlgebraicEquivalence

open AlgebraicGeometry CategoryTheory Limits

universe u


namespace CartierDivisorGroup

/-- An *irreducible complete curve* over `S`: an integral scheme together with a proper structure
morphism to `S`. -/
structure IrredCompleteCurve (S : Scheme.{u}) where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ S
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  isProper : IsProper structureMorphism

/-- A morphism of `S`-curves: a scheme morphism over `S`. -/
structure CurveMorphism {S : Scheme.{u}}
    (X Y : IrredCompleteCurve S) where
  morphism : X.toScheme ⟶ Y.toScheme
  compatible : morphism ≫ Y.structureMorphism = X.structureMorphism

end CartierDivisorGroup
end AlgebraicEquivalence
end
