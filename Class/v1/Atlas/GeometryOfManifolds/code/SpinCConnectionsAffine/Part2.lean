/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SpinCConnectionsAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
import Structure.v1.Atlas.GeometryOfManifolds.code.SpinCConnectionsAffine.Part2
set_option autoImplicit false


attribute [instance] DeterminantLineBundle.instACGL DeterminantLineBundle.instModL


/-- **A spin-c connection is determined by its induced connection on the determinant line
bundle $L = \wedge^2 S^+$.** The map sending a spin-c connection $A$ to the induced
connection on $L$ is a bijection. -/
class SpinCConnectionDetermination
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2)
    [aff : SpinCConnectionsAffine spinc] where
  ConnectionOnL : Type
  induced_on_L : aff.ConnectionSpace → ConnectionOnL
  connection_determines_spinc : ∀ (A₁ A₂ : aff.ConnectionSpace),
    induced_on_L A₁ = induced_on_L A₂ → A₁ = A₂
  connection_surjective : ∀ (B : ConnectionOnL),
    ∃ (A : aff.ConnectionSpace), induced_on_L A = B

