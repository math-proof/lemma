/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance
import Lemma.Submodule.Any_EqMapToLinearMap.of.FinrankK
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyInstance


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


/-- Bundles `opposite_systems_conjugacy_theorem` as an instance of the
`OppositeSystemsConjugacyProperty` typeclass. -/
def instOppositeSystemsConjugacyProperty' [FiniteDimensional k V]
    (hyp : OppositeConjugacyCompositionHyp k V) :
    OppositeSystemsConjugacyProperty k V where
  conjugate_linear := fun F F'₁ F'₂ h₁ h₂ =>
    opposite_systems_conjugacy_theorem k V hyp F F'₁ F'₂ h₁ h₂

end GeometricAlgebra
