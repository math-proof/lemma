/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeCInjectivityHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.SetTheory.Cardinal.Finite
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
open Equiv Fin Function SignedPerm


/-- The $i$-th Coxeter generator of type $C_n$: an adjacent transposition for $i < n-1$, or the
sign change at the last coordinate when $i = n-1$. -/
noncomputable def typeCGen {n : ℕ} (i : Fin n) : SignedPermGroup n :=
  if h : (i : ℕ) + 1 < n then
    SemidirectProduct.inr (Equiv.swap (i : Fin n) ⟨i + 1, h⟩)
  else
    SemidirectProduct.inl (signChangeAt n ⟨n - 1, by omega⟩)

