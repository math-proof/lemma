/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Def.v1.Atlas.AlgebraicGeometryI.code.GrassmannianProjective
open scoped LinearAlgebra.Projectivization
open ExteriorAlgebra

public section

namespace GrassmannianProjective

variable {K : Type*} [Field K]

section PluckerEmbedding

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

omit [Module.Free K V] in
/-- The Plücker coordinate of a `k`-dimensional subspace is nonzero, so it defines a point in `P(⋀^k V)`. -/
theorem plucker_coord_ne_zero (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) :
    pluckerCoord K V k W hk ≠ 0 := by
  unfold pluckerCoord
  intro h

  obtain ⟨Q, hQ⟩ := W.exists_isCompl
  have hinj := exteriorPower.map_injective
    (Submodule.linearProjOfIsCompl W Q hQ)
    (Submodule.linearProjOfIsCompl_comp_subtype hQ) (n := k)

  have hne : (exteriorPower.ιMulti K k
      (fun i => (subspaceBasis K V k W hk) i)) ≠ 0 :=
    ιMulti_basis_ne_zero (subspaceBasis K V k W hk)
  exact hne (hinj (by rwa [map_zero]))

end PluckerEmbedding
end GrassmannianProjective
