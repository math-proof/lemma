/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorem.v1.Atlas.AlgebraicGeometryI.code.GrassmannianProjective
open scoped LinearAlgebra.Projectivization
open ExteriorAlgebra


namespace GrassmannianProjective

variable {K : Type*} [Field K]

section GrassmannianDef

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

/-- The Grassmannian `Gr(k, V)` as a set of `k`-dimensional subspaces of `V`. -/
def SubspaceGr (k : ℕ) := {W : Submodule K V // Module.finrank K W = k}

end GrassmannianDef

section PluckerEmbedding

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- Choose a basis `Fin k → W` for a `k`-dimensional subspace `W` of `V`. -/
noncomputable def subspaceBasis (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) : Module.Basis (Fin k) K W :=
  (Module.finBasis K W).reindex (Fin.castOrderIso hk).toEquiv

/-- Plücker coordinate of `W`: the image of `e_1 ∧ ... ∧ e_k` in `⋀^k V` under the inclusion. -/
noncomputable def pluckerCoord (k : ℕ) (W : Submodule K V)
    (hk : Module.finrank K W = k) : ↥(⋀[K]^k V) :=
  let b := subspaceBasis K V k W hk
  exteriorPower.map k W.subtype (exteriorPower.ιMulti K k (fun i => b i))

end PluckerEmbedding
end GrassmannianProjective
