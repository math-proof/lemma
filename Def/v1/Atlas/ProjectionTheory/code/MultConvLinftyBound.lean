/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvLinftyBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.ProjectionTheory.code.HighFreqMultConv
public import Theorem.Real.Atlas.v1.ProjectionTheory.code.HighFreqMultConv
public import Theorem.Real.Atlas.v1.ProjectionTheory.code.BKTLemma2
public import Theorem.Real.Atlas.v1.ProjectionTheory.code.BKTLemma3
public import Theorem.Real.Atlas.v1.ProjectionTheory.code.MultConvProjection
public import Def.v1.Atlas.ProjectionTheory.code.BKTLemma2
public import Def.v1.Atlas.ProjectionTheory.code.BKTLemma3
public import Def.v1.Atlas.ProjectionTheory.code.MultConvProjection

@[expose] public section

open Finset Complex BigOperators


noncomputable section

namespace HighFreqMultConv

variable (q : ℕ) [NeZero q] [Fact (Nat.Prime q)]

/-- The $L^2$ norm of $f : (\mathbb{Z}/q)^* \to \mathbb{C}$ on the unit group,
$\|f\|_{L^2((\mathbb{Z}/q)^*)} = \bigl(\sum_{b \in (\mathbb{Z}/q)^*} |f(b)|^2\bigr)^{1/2}$. -/
def l2NormUnits (f : (ZMod q)ˣ → ℂ) : ℝ :=
  Real.sqrt (∑ b : (ZMod q)ˣ, ‖f b‖ ^ 2)

/-- Restrict a function $F : \mathbb{Z}/q \to \mathbb{C}$ to the unit group
$(\mathbb{Z}/q)^*$ by composing with the natural map $u \mapsto (u : \mathbb{Z}/q)$. -/
def restrictToUnits (F : ZMod q → ℂ) : (ZMod q)ˣ → ℂ :=
  fun u => F (↑u : ZMod q)

/-- The $L^2$ norm of $F : \mathbb{Z}/q \to \mathbb{C}$,
$\|F\|_{L^2(\mathbb{Z}/q)} = \bigl(\sum_{a} |F(a)|^2\bigr)^{1/2}$. -/
def l2Norm_ZMod (F : ZMod q → ℂ) : ℝ :=
  Real.sqrt (LinnikLargeSieve.l2NormSq_ZMod q F)

end HighFreqMultConv
end
