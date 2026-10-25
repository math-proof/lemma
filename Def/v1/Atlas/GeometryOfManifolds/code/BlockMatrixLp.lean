/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BlockMatrixLp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Structure.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
set_option autoImplicit false

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]


/-- The "untwisted" model symplectic form
$\omega_0((v_1,w_1),(v_2,w_2)) = \mathrm{eval}(w_1, v_2) - \mathrm{eval}(w_2, v_1)$
on $V \times W$. -/
noncomputable def BlockSymplecticData.omega0 (d : BlockSymplecticData V W)
    (p₁ p₂ : V × W) : ℝ :=
  d.eval p₁.2 p₂.1 - d.eval p₂.2 p₁.1

/-- The "twisted" symplectic form
$\omega_1((v_1,w_1),(v_2,w_2)) = \mathrm{eval}(w_1, Bv_2) - \mathrm{eval}(w_2, Bv_1) + C(w_1,w_2)$
obtained by composing the $V$-pairing with $B$ and adding the skew form $C$ on $W$. -/
noncomputable def BlockSymplecticData.omega1 (d : BlockSymplecticData V W)
    (p₁ p₂ : V × W) : ℝ :=
  d.eval p₁.2 (d.B_endo p₂.1) - d.eval p₂.2 (d.B_endo p₁.1) + d.C_form p₁.2 p₂.2

/-- Block linear change of variables $(v,w) \mapsto (v - \tfrac{1}{2} B^{-1} \tilde C (B^{-T} w), B^{-T} w)$
used to relate the twisted symplectic form $\omega_1$ back to the model form $\omega_0$. -/
noncomputable def BlockSymplecticData.correctionMap (d : BlockSymplecticData V W)
    (p : V × W) : V × W :=
  (p.1 + ((-1 : ℝ)/2) • d.B_inv (d.C_tilde (d.B_inv_t p.2)), d.B_inv_t p.2)

