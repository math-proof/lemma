/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityConcrete.Part3
set_option autoImplicit false


namespace EllipticRegularityConcrete

/-- A smoothing (regularity-improving) operator: it gains one derivative in the Sobolev
scale and maps anything with finite Sobolev regularity into the smooth class $C^\infty$. -/
structure IsSmoothingOperator {n k : ℕ} (snorms : SobolevNorms n k)
    (S : DiffForm n (k + 1) → DiffForm n (k + 1)) where
  regularity_gain : ∀ (s : ℕ), ∃ (C : ℝ), C > 0 ∧
    ∀ (ξ : DiffForm n (k + 1)), snorms.norm (s + 1) (S ξ) ≤ C * snorms.norm s ξ
  maps_to_smooth : ∀ (s : ℕ) (ξ : DiffForm n (k + 1)),
    HasSobolevRegularity snorms s ξ → IsSmoothForm (S ξ)


/-- A concrete parametrix for an elliptic operator $L$: an approximate inverse $P$ with
$P \circ L = \mathrm{Id} + S$ for a smoothing remainder $S$. This is the key analytic input
for the elliptic regularity theorem $L\xi \in C^\infty \Rightarrow \xi \in C^\infty$. -/
structure ConcreteParametrix {n : ℕ} (k : ℕ)
    (L : DiffForm n (k + 1) → DiffForm n (k + 1)) where
  P : DiffForm n (k + 1) → DiffForm n (k + 1)
  S_left : DiffForm n (k + 1) → DiffForm n (k + 1)
  sobolevNorms : SobolevNorms n k
  PL_eq : ∀ (ξ : DiffForm n (k + 1)), P (L ξ) = ξ + S_left ξ
  S_left_smoothing : IsSmoothingOperator sobolevNorms S_left


end EllipticRegularityConcrete
