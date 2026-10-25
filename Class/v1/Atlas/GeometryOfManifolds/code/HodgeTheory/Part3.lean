/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part7
set_option autoImplicit false

open DifferentialFormSpace


/-- A predicate giving the Sobolev regularity scale $H^s$ for differential forms. -/
class HasSobolevSpaces (Ω : ℕ → Type*) (VF : Type*) [DifferentialFormSpace Ω VF] where
  IsSobolevRegular : ℕ → ∀ {p : ℕ}, Ω (p + 1) → Prop


/-- A *smoothing operator* $S$: linear and raises Sobolev regularity by at least one
order (and by two when iterated). -/
class IsSmoothing {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [sob : HasSobolevSpaces Ω VF]
    (S : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) : Prop where
  S_add : ∀ {p : ℕ} (a b : Ω (p + 1)), S (a + b) = S a + S b
  S_smul : ∀ {p : ℕ} (r : ℝ) (a : Ω (p + 1)), S (r • a) = r • S a
  sobolev_improvement : ∀ (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular (s + 1) (S α)
  compact_improvement : ∀ (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular (s + 2) (S (S α))


