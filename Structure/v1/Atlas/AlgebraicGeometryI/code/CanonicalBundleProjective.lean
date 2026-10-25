/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafDef
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf.Part2
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part2


noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section MvPolynomialSmooth

variable (k : Type u) [Field k] (n : ℕ)

/-- A short exact sequence of graded `k`-modules on `P^n`, given by maps in every degree
together with proofs of injectivity, surjectivity and exactness in the middle. -/
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

end MvPolynomialSmooth
end
