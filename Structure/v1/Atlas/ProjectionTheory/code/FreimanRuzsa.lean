/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/FreimanRuzsa.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset Pointwise


namespace FreimanRuzsa

/-- A generalized arithmetic progression (GAP) in an abelian group $\alpha$: a base point,
a `dim`-dimensional family of step directions $v_1,\dots,v_{\dim}$, and integer lengths
$N_1,\dots,N_{\dim}$, representing the set
$\{\text{base} + n_1 v_1 + \dots + n_{\dim} v_{\dim} : 0 \le n_i < N_i\}$. -/
structure GAP (α : Type*) [AddCommGroup α] where
  dim : ℕ
  base : α
  dirs : Fin dim → α
  lengths : Fin dim → ℕ

end FreimanRuzsa
