/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/GSW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.OSRWSharp
open Classical


noncomputable section

namespace ProjectionTheory

/-- The *richness* of a `δ`-tube `T` with respect to a point set `E` is the number of
points of `E` contained in `T`. -/
noncomputable def DeltaTube.richness (T : DeltaTube) (E : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (E.filter (fun x => T.contains x)).card

/-- Two `δ`-tubes are *essentially distinct* at scale `δ` if either their midpoints are more
than `δ` apart, or their directions differ by more than `δ`. -/
def DeltaTube.EssentiallyDistinct (T₁ T₂ : DeltaTube) (δ : ℝ) : Prop :=
  dist T₁.midpoint T₂.midpoint > δ ∨ |T₁.direction - T₂.direction| > δ

/-- A finite point set `E ⊆ ℝ²` is *well-spaced* with constant `C₀` if every ball of radius
`|E|^(-1/2)` contains at most `C₀` points of `E`, i.e. $|E \cap B_{|E|^{-1/2}}| \lesssim 1$. -/
def IsWellSpaced (E : Finset (EuclideanSpace ℝ (Fin 2))) (C₀ : ℝ) : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin 2),
    ((E.filter (fun x => dist x c ≤ (E.card : ℝ) ^ (-(1 : ℝ) / 2))).card : ℝ) ≤ C₀

end ProjectionTheory
end
