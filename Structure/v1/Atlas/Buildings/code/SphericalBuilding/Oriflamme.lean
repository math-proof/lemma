/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Submodule.Any_EqAndAll_Eq_V.of.IsSubspaceIsometry.EqOrthogonalBilinFormTop_Bot.All_Eq
import Def.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part2


namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- The **oriflamme complex** on $(V, B)$: a flag complex of oriflamme vertices, pairwise
incident, closed under nonempty subsets. -/
structure OriflammeComplex where
  simplices : Set (Finset (Submodule k V))
  simplex_vertices : ∀ σ ∈ simplices, ∀ W ∈ σ, IsOriflammeVertex k V B n W
  simplex_incident : ∀ σ ∈ simplices, ∀ W₁ ∈ σ, ∀ W₂ ∈ σ,
    OriflammeIncident k V n W₁ W₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (Submodule k V),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


/-- An **oriflamme chamber**: a maximal simplex in the oriflamme complex, consisting of an
isotropic chain $W_1 \subsetneq \cdots \subsetneq W_{n-2}$ of dimensions $1, \dots, n-2$
together with two distinct maximal isotropic $n$-subspaces $V_1 \ne V_2$ both containing
$W_{n-2}$ and meeting in dimension $n - 1$. -/
structure OriflammeChamber where
  chain : Fin (n - 2) → Submodule k V
  top₁ : Submodule k V
  top₂ : Submodule k V
  chain_strictMono : StrictMono chain
  chain_isotropic : ∀ i, IsTotallyIsotropic k V B (chain i)
  chain_dim : ∀ i : Fin (n - 2), Module.finrank k (chain i) = i.val + 1
  top₁_isotropic : IsTotallyIsotropic k V B top₁
  top₂_isotropic : IsTotallyIsotropic k V B top₂
  top₁_dim : Module.finrank k top₁ = n
  top₂_dim : Module.finrank k top₂ = n
  top₁_ne_top₂ : top₁ ≠ top₂
  chain_sub_tops : ∀ (h : 0 < n - 2), chain ⟨n - 3, by omega⟩ ≤ top₁ ⊓ top₂
  inter_dim : Module.finrank k ↥(top₁ ⊓ top₂) = n - 1


/-- An **oriflamme frame** of $(V, B)$: a hyperbolic frame as a decomposition into $n$
hyperbolic planes (one per index $i \in \mathrm{Fin}\, n$), each plane spanned by two isotropic
lines indexed by `Bool`. -/
structure OriflammeFrame where
  lines : Fin n × Bool → Submodule k V
  lines_isotropic : ∀ ib, IsTotallyIsotropic k V B (lines ib)
  lines_dim_one : ∀ ib, Module.finrank k (lines ib) = 1
  planes : Fin n → Submodule k V
  planes_eq : ∀ i, planes i = lines (i, true) ⊔ lines (i, false)
  span_top : ⨆ i, planes i = ⊤

end Oriflamme
