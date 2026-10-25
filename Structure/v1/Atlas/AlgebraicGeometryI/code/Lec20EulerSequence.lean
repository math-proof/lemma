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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec20EulerSequence
set_option maxHeartbeats 800000

open QCohProjective TwistSheaf


noncomputable section

namespace EulerSequence

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-- A short exact sequence `0 → L → M → R → 0` of graded module data, with degree-wise
injectivity, surjectivity, and exactness at the middle. -/
structure GradedSES where
  left : GradedModuleData.{u, u} k n
  middle : GradedModuleData.{u, u} k n
  right : GradedModuleData.{u, u} k n
  f : ∀ d : ℤ, GrLinMap k n left middle d
  g : ∀ d : ℤ, GrLinMap k n middle right d
  f_injective : ∀ d : ℤ, Function.Injective (f d)
  g_surjective : ∀ d : ℤ, Function.Surjective (g d)
  exact_middle : ∀ (d : ℤ) (x : middle.component d),
    @Eq (right.component d) (g d x)
      (@Zero.zero (right.component d) (right.instACG d).toAddCommMonoid.toZero) ↔
    ∃ a : left.component d, (f d) a = x

end EulerSequence
end
