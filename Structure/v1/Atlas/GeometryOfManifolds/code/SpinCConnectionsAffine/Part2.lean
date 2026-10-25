/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SpinCConnectionsAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
import Class.v1.Atlas.GeometryOfManifolds.code.SpinCConnectionsAffine
set_option autoImplicit false


/-- Construction of the affine-space-over-$\Omega^1$ structure on spin-c connections, for an
arbitrary spin-c structure on $M$. -/
structure DeterminantLineBundle
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  SectionsL : Type
  [instACGL : AddCommGroup SectionsL]
  [instModL : Module ℝ SectionsL]
  wedge_product : spinc.SectionsPlus → spinc.SectionsPlus → SectionsL
  wedge_antisymm : ∀ (ψ φ : spinc.SectionsPlus),
    wedge_product ψ φ = -wedge_product φ ψ

