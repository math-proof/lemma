/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20EulerSequence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleProjective
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part4
set_option maxHeartbeats 800000

open QCohProjective TwistSheaf


noncomputable section

namespace EulerSequence

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- A `k`-linear map between the degree-`d` components of two graded module data over `ℙⁿ`. -/
abbrev GrLinMap (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearMap k k _ _ (RingHom.id k) (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

/-- A `k`-linear equivalence between the degree-`d` components of two graded module data. -/
abbrev GrLinEquiv (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k)
    ⟨RingHom.id_comp _, RingHom.comp_id _⟩ ⟨RingHom.id_comp _, RingHom.comp_id _⟩
    (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

end EulerSequence
end
