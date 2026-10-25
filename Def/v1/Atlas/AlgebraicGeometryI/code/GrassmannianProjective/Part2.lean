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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.GrassmannianProjective.Part2
open scoped LinearAlgebra.Projectivization
open ExteriorAlgebra


namespace GrassmannianProjective

variable {K : Type*} [Field K]

section PluckerEmbedding

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- Plücker map `Gr(k, V) → P(⋀^k V)` sending `W` to the projective class of `e_1 ∧ ... ∧ e_k`. -/
noncomputable def pluckerMap (k : ℕ) : SubspaceGr K V k → ℙ K (⋀[K]^k V) :=
  fun ⟨W, hk⟩ => Projectivization.mk K (pluckerCoord K V k W hk) (plucker_coord_ne_zero K V k W hk)

/-- A `k`-vector `ω ∈ ⋀^k V` is decomposable if it can be written as a wedge `v_1 ∧ ... ∧ v_k`. -/
def IsDecomposableExtPower (k : ℕ) (ω : ⋀[K]^k V) : Prop :=
  ∃ (v : Fin k → V), ω = exteriorPower.ιMulti K k v

/-- The locus of decomposable classes in `P(⋀^k V)`, i.e. the image of the Plücker map. -/
def DecomposableProjective (k : ℕ) : Set (ℙ K (⋀[K]^k V)) :=
  {p | ∃ (v : Fin k → V) (hv : exteriorPower.ιMulti K k v ≠ 0),
    p = Projectivization.mk K (exteriorPower.ιMulti K k v) hv}

/-- A subset of `P(⋀^k V)` is Zariski closed by quadratics if it is the zero locus of
homogeneous degree-2 polynomial functions (the Plücker relations). -/
def IsZariskiClosedByQuadratics (k : ℕ) (S : Set (ℙ K (⋀[K]^k V))) : Prop :=
  ∃ (ι : Type) (polys : ι → (⋀[K]^k V) → K),
    (∀ i, ∀ (c : K) (v : ⋀[K]^k V), polys i (c • v) = c ^ 2 * polys i v) ∧
    S = {p : ℙ K (⋀[K]^k V) | ∃ (v : ⋀[K]^k V) (hv : v ≠ 0),
      p = Projectivization.mk K v hv ∧ ∀ i, polys i v = 0}

/-- The image of the Plücker embedding is cut out by quadratic Plücker relations. -/

end PluckerEmbedding

section PluckerRelation

variable {K : Type*} [CommRing K] {M : Type*} [AddCommGroup M] [Module K M]

/-- A degree-2 element of the exterior algebra is decomposable if it equals a single wedge `v₁ ∧ v₂`. -/
def IsDecomposableDeg2 (ω : ExteriorAlgebra K M) : Prop :=
  ∃ v₁ v₂ : M, ω = ι K v₁ * ι K v₂

end PluckerRelation
end GrassmannianProjective
