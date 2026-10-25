/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Def.v1.Atlas.GeometryOfManifolds.code.DolbeaultHodgeMathlib.Part2
set_option autoImplicit false

open ContinuousAlternatingMap


namespace DolbeaultHodgeMathlib

/-- Axiomatic Dolbeault data: the operators $\bar\partial$, its formal adjoint $\bar\partial^*$,
and the $\bar\partial$-Laplacian $\bar\square = \bar\partial \bar\partial^* + \bar\partial^*
\bar\partial$, satisfying $\bar\partial^2 = 0$ and linearity. -/
structure DolbeaultData (n : ℕ) where
  delbar : ∀ {k : ℕ}, DiffForm n k → DiffForm n (k + 1)
  delbar_star : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n k
  box_bar : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)
  delbar_sq : ∀ {k : ℕ} (α : DiffForm n k), delbar (delbar α) = 0
  delbar_add : ∀ {k : ℕ} (α β : DiffForm n k), delbar (α + β) = delbar α + delbar β
  delbar_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n k), delbar (r • α) = r • delbar α
  box_bar_eq : ∀ {k : ℕ} (α : DiffForm n (k + 1)),
    box_bar α = delbar (delbar_star α) + delbar_star (delbar α)
  delbar_star_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)),
    delbar_star (r • α) = r • delbar_star α

/-- The adjointness relation $\langle \bar\partial \alpha, \beta \rangle = \langle \alpha,
\bar\partial^* \beta \rangle$ between $\bar\partial$ and $\bar\partial^*$. -/
structure HasDelbarAdjoint {n : ℕ} (ip : L2InnerProduct n) (dol : DolbeaultData n) : Prop where
  adj : ∀ {k : ℕ} (α : DiffForm n k) (β : DiffForm n (k + 1)),
    ip.inner (dol.delbar α) β = ip.inner α (dol.delbar_star β)

end DolbeaultHodgeMathlib
