/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SpinCConnectionsAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
import Structure.v1.Atlas.GeometryOfManifolds.code.SpinCConnectionsAffine
set_option autoImplicit false


/-- The space of spin-c connections is an **affine space over $\Omega^1(M)$**: any two
connections differ by a $1$-form, translation by $0$ is the identity, and translation is
additive. This is the abstract statement that "any two spin-c connections differ by
$ia \otimes \mathrm{id}_{S^\pm}$". -/
class SpinCConnectionsAffine
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  ConnectionSpace : Type
  translate : Ω1 → ConnectionSpace → ConnectionSpace
  difference : ConnectionSpace → ConnectionSpace → Ω1
  translate_difference : ∀ (A B : ConnectionSpace), translate (difference A B) B = A
  difference_translate : ∀ (a : Ω1) (A : ConnectionSpace), difference (translate a A) A = a
  translate_zero : ∀ (A : ConnectionSpace), translate 0 A = A
  translate_add : ∀ (a b : Ω1) (A : ConnectionSpace),
    translate a (translate b A) = translate (a + b) A

