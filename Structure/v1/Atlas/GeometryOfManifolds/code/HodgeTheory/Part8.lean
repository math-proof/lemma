/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Class.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- A smoothing operator $S: E \to E$ on an abstract topological vector space, characterized
by raising the Sobolev regularity by one order. -/
structure IsSmoothingOp {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    (S : E →L[ℝ] E)
    (IsSobReg : ℕ → E → Prop) : Prop where
  sobolev_improvement : ∀ (s : ℕ) (α : E),
    IsSobReg s α → IsSobReg (s + 1) (S α)

/-- A parametrix (pseudo-inverse) for a continuous linear operator $L: E \to F$:
a continuous linear $P: F \to E$ with $PL = \mathrm{id} + S_{\text{left}}$ and
$LP = \mathrm{id} + S_{\text{right}}$, where $S_{\text{left}}$ and $S_{\text{right}}$
are smoothing operators. -/
structure HasParametrix
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    (L : E →L[ℝ] F) where
  P : F →L[ℝ] E
  S_left : E →L[ℝ] E
  S_right : F →L[ℝ] F
  PL_eq : ∀ (α : E), P (L α) = α + S_left α
  LP_eq : ∀ (β : F), L (P β) = β + S_right β
  IsSobRegE : ℕ → E → Prop
  IsSobRegF : ℕ → F → Prop
  isSmoothingOp_S_left : IsSmoothingOp S_left IsSobRegE
  isSmoothingOp_S_right : IsSmoothingOp S_right IsSobRegF

