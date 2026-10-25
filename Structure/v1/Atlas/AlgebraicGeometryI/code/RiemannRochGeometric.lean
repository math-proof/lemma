/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
open AlgebraicGeometry CategoryTheory


noncomputable section

namespace RiemannRochGeometric

/-- Axiomatic data for a smooth complete curve `X` over a field `k`, together
with cohomology dimensions and the Riemann–Roch ingredients (rank, degree,
arithmetic genus) needed for Thm 24.2 (Lec 24). -/
structure SmoothCurveWithCohomology (k : Type) [Field k] where
  X : Scheme
  f : X ⟶ Spec (CommRingCat.of k)
  [isIntegral : AlgebraicGeometry.IsIntegral X]
  [isProper : IsProper f]
  [isSmooth : SmoothOfRelativeDimension 1 f]
  dimH0 : X.Modules → ℕ
  dimH1 : X.Modules → ℕ
  degree : X.Modules → ℤ
  sheafRank : X.Modules → ℤ
  arithmeticGenus : ℕ
  chiK0 : ℤ × ℤ →+ ℤ
  chi_eq_chiK0 : ∀ F : X.Modules,
    (dimH0 F : ℤ) - (dimH1 F : ℤ) = chiK0 (sheafRank F, degree F)
  chi_structureSheaf : chiK0 (1, 0) = 1 - (arithmeticGenus : ℤ)
  chi_skyscraper : chiK0 (0, 1) = 1

end RiemannRochGeometric
end
