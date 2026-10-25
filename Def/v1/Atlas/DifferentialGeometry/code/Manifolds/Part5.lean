/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds.Part5


noncomputable section

open scoped Topology

open LinearMap (ker range)

open Set Filter

variable {n : ℕ}

namespace Hypersurface.Curvature

open scoped InnerProductSpace

open Finset

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussCurvatureMatrix (ψ : E → ℝ) (y : E) (Y : Fin n → E)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun j i =>
    if h : (i : ℕ) < n then
      (fderiv ℝ (fderiv ℝ ψ) y) (Y ⟨i, h⟩) (b j)
    else
      (fderiv ℝ ψ y) (b j)

def gaussCurvatureLevelSet (ψ : E → ℝ) (y : E) (Y : Fin n → E)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) : ℝ :=
  (gaussCurvatureMatrix ψ y Y b).det / ‖fderiv ℝ ψ y‖ ^ (n + 1)

def shapeOperatorLevelSet (ψ : E → ℝ) (y : E) (Y : Fin n → E) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (1 / ‖fderiv ℝ ψ y‖) * (fderiv ℝ (fderiv ℝ ψ) y) (Y i) (Y j)

end Hypersurface.Curvature
end
