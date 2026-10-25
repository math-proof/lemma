/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticStandardBasis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticEvenDim
open Module FiniteDimensional


namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A standard symplectic basis $\{e_i, f_i\}_{i=1}^n$ for $(V, \Omega)$: the $e_i, f_i$ form a
basis of $V$ and satisfy $\Omega(e_i, e_j) = \Omega(f_i, f_j) = 0$ and $\Omega(e_i, f_j) =
\delta_{ij}$. -/
structure SymplecticBasis {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Ω : LinearMap.BilinForm ℝ V) where
  n : ℕ
  e : Fin n → V
  f : Fin n → V
  basis : Basis (Fin n ⊕ Fin n) ℝ V
  basis_eq_e : ∀ i, basis (Sum.inl i) = e i
  basis_eq_f : ∀ i, basis (Sum.inr i) = f i
  omega_ee : ∀ i j, Ω (e i) (e j) = 0
  omega_ff : ∀ i j, Ω (f i) (f j) = 0
  omega_ef : ∀ i j, Ω (e i) (f j) = if i = j then 1 else 0

end SymplecticLinearAlgebra
