/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Intrinsic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Structure.v1.Atlas.DifferentialGeometry.code.Intrinsic


noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

namespace ChristoffelFromMetric

open ChristoffelSymbols

def christoffelMatrix (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => ChristoffelSymbols.christoffelSymbol patch x i j k

def matrixPartialDeriv
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fderiv ℝ X x (Pi.single j 1)

def connectionMatrix (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  let Xinv := (X x)⁻¹
  let dX := matrixPartialDeriv X x j
  let Γ := christoffelMatrix patch x j
  Xinv * dX + Xinv * Γ * (X x)

def curvatureMatrix (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (k j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  let A := connectionMatrix patch X
  let dkAj := fderiv ℝ (fun y => A y j) x (Pi.single k 1)
  let djAk := fderiv ℝ (fun y => A y k) x (Pi.single j 1)
  dkAj - djAk + (A x k) * (A x j) - (A x j) * (A x k)

def riemannCurvatureMatrix (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (k j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fderiv ℝ (fun y => christoffelMatrix patch y j) x (Pi.single k 1) -
  fderiv ℝ (fun y => christoffelMatrix patch y k) x (Pi.single j 1) +
  christoffelMatrix patch x k * christoffelMatrix patch x j -
  christoffelMatrix patch x j * christoffelMatrix patch x k


def metricPartialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  matrixPartialDeriv (firstFundamentalForm patch) x j

def transformedMetricLinear
    (G B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Bᵀ * G * B

def metricDerivAfterQuadraticChange
    (S T : Fin n → Fin n → Fin n → ℝ) (i j k : Fin n) : ℝ :=
  S i j k - T i j k - T j i k

def riemannCurvature (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  riemannCurvatureMatrix patch x j k i s

noncomputable def riemannCurvature {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  partialDeriv k (fun y => christoffelSymbol patch y i j s) x -
  partialDeriv j (fun y => christoffelSymbol patch y i k s) x +
  ∑ t, (christoffelSymbol patch x i j t * christoffelSymbol patch x k t s -
       christoffelSymbol patch x i k t * christoffelSymbol patch x j t s)

noncomputable def thirdPartialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k : Fin n) : Fin (n + 1) → ℝ :=
  fderiv ℝ (fun y => secondPartialDeriv patch y i j) x (Pi.single k 1)

noncomputable def thirdDerivTangComp (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  ((firstFundamentalForm patch x)⁻¹ *ᵥ
    (fun l => (thirdPartialDeriv patch x i j k) ⬝ᵥ (patch.partialDeriv x l))) s

noncomputable def exteriorPowerShapeOp (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  shapeOperator patch x i k * shapeOperator patch x j s -
  shapeOperator patch x i s * shapeOperator patch x j k

noncomputable def exteriorPowerShapeOpMatrix (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  Matrix.of (fun p q => exteriorPowerShapeOp patch x p.1 p.2 q.1 q.2)

end ChristoffelFromMetric
end ChristoffelSymbols
end
