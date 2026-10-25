/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Derivation.Lie
import Def.v1.Atlas.LieGroups.code.DModules.Part3
universe u v w


namespace DModules

open scoped TensorProduct

section Prop289

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]

variable {M : Type w} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

theorem liftKaehlerDifferential_smul (f : A) (v : Derivation k A A) :
    (f • v).liftKaehlerDifferential = f • v.liftKaehlerDifferential := by
  apply Derivation.liftKaehlerDifferential_unique
  ext g
  simp [Derivation.liftKaehlerDifferential_comp_D, LinearMap.compDer]

end Prop289
end DModules
