/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Def.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part2
set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


namespace WeinsteinNeighborhood

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The induced map $V/E \to E^*$ is injective for $E$ Lagrangian, because the kernel
of the original map is exactly $E^{\perp_\Omega} = E$. -/
lemma quotientToDual_injective [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    Function.Injective (quotientToDual hΩ hE) := by
  rw [← LinearMap.ker_eq_bot]
  unfold quotientToDual
  rw [Submodule.ker_liftQ]
  rw [symplecticToDual_ker hΩ]
  unfold IsLagrangian at hE
  rw [hE]
  exact Submodule.mkQ_map_self E

/-- For $E$ a Lagrangian subspace, $\dim(V/E) = \dim E^* = \dim E$, since
$\dim E = \tfrac12 \dim V$. -/
lemma quotient_finrank_eq_dual [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    finrank ℝ (V ⧸ E) = finrank ℝ (Dual ℝ E) := by
  rw [Subspace.dual_finrank_eq]
  have hq := Submodule.finrank_quotient_add_finrank E
  have h2 := lagrangian_half_dim hΩ hE
  omega


end WeinsteinNeighborhood
