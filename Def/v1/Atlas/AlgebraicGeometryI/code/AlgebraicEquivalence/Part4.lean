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
import Structure.v1.Atlas.AlgebraicGeometryI.code.AlgebraicEquivalence.Part2


noncomputable section

namespace AlgebraicEquivalence

open AlgebraicGeometry CategoryTheory Limits

universe u


namespace CartierDivisorGroup

/-- A morphism of curves is *constant* if it is not dominant. -/
def CurveMorphism.IsConstant {S : Scheme.{u}}
    {X Y : IrredCompleteCurve S} (f : CurveMorphism X Y) : Prop :=
  ¬ IsDominant f.morphism

end CartierDivisorGroup
end AlgebraicEquivalence
end
