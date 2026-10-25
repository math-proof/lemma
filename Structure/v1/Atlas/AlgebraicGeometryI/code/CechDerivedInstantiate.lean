/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CechDerivedInstantiate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicGeometryI.code.CohomologyConnection
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyConnection
import Def.v1.Atlas.AlgebraicGeometryI.code.CechDerivedInstantiate


noncomputable section

open CategoryTheory CategoryTheory.Limits

open SheafCohomology CohomologyP1 DerivedFunctorsDefs


namespace DerivedFunctorsDefs

universe v₀ u₀

variable {C : Type u₀} [Category.{v₀} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- Witness data packaging the basic facts about Čech-versus-derived cohomology of line bundles
on `P¹`: vanishing of `H¹` for nonnegative twists, the Euler characteristic formula, an
effaceability witness, and Serre duality. -/
structure CechToDerivedDataP1Witness (k : Type) [Field k] where
  h1_vanishing : ∀ n : ℤ, 0 ≤ n → Module.finrank k (H1 k n) = 0
  euler_char : ∀ n : ℤ,
    (Module.finrank k (H0 k n) : ℤ) -
    (Module.finrank k (H1 k n) : ℤ) = n + 1
  effaceability : ∀ n : ℤ,
    ∃ N : ℤ, 0 ≤ N ∧ n ≤ N ∧ Module.finrank k (H1 k N) = 0
  serre_duality : ∀ n : ℤ,
    Module.finrank k (H1 k n) =
    Module.finrank k (H0 k (-2 - n))

end DerivedFunctorsDefs
end
