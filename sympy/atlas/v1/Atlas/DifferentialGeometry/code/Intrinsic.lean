/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Intrinsic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
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

noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

def secondPartialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j : Fin n) : Fin (n + 1) → ℝ :=
  fderiv ℝ (fun y => fderiv ℝ patch.f y (Pi.single j 1)) x (Pi.single i 1)

noncomputable def christoffelSymbol (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k : Fin n) : ℝ :=
  let G := firstFundamentalForm patch x
  let d2f := secondPartialDeriv patch x i j
  let tangentialCoeffs : Fin n → ℝ := fun l => d2f ⬝ᵥ (patch.partialDeriv x l)
  ((G⁻¹) *ᵥ tangentialCoeffs) k

noncomputable def partialDeriv {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single i 1)

namespace ChristoffelFromMetric

open ChristoffelSymbols

noncomputable def tensorT (S : ι → ι → ι → F) (i j k : ι) : F :=
  (S i j k + S j k i - S k i j) / 2

structure IsMovingBasis (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop where
  smooth : ContDiffOn ℝ ⊤ X patch.domain
  invertible : ∀ x ∈ patch.domain, IsUnit (X x)

structure IsMovingFrame (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop extends IsMovingBasis patch X where
  orthonormal : ∀ x ∈ patch.domain,
    (X x)ᵀ * firstFundamentalForm patch x * (X x) = 1

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

abbrev AntisymIndex (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

noncomputable def exteriorPowerShapeOpMatrix_antisym (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (AntisymIndex n) (AntisymIndex n) ℝ :=
  Matrix.of (fun p q => exteriorPowerShapeOp patch x p.val.1 p.val.2 q.val.1 q.val.2)

def riemannCurvature (patch : HypersurfacePatch 2)
    (x : Fin 2 → ℝ) (i j k s : Fin 2) : ℝ :=
  GaussEquation.riemannCurvature patch x i j k s

end TheoremaEgregium

namespace GaussBonnetTorus

open MeasureTheory MovingFrame

structure RiemannianMetric (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  domain_nonempty : domain.Nonempty
  G : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  smooth : ContDiffOn ℝ ⊤ G domain
  symmetric : ∀ x ∈ domain, (G x)ᵀ = G x
  posDef : ∀ x ∈ domain, (G x).PosDef

end AbstractRiemannianMetric

namespace AbstractGaussBonnet

open MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure RiemannianMetric2D where
  G : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ
  smooth : ContDiff ℝ ⊤ G
  symmetric : ∀ x, (G x)ᵀ = G x
  posDef : ∀ x, (G x).PosDef

def scalarPartialDeriv (i : Fin 2) (f : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

def abstractChristoffel (g : RiemannianMetric2D) (x : Fin 2 → ℝ)
    (i j k : Fin 2) : ℝ :=
  (1/2) * ∑ l, (g.G x)⁻¹ l k *
    (scalarPartialDeriv j (fun y => g.G y i l) x +
     scalarPartialDeriv i (fun y => g.G y j l) x -
     scalarPartialDeriv l (fun y => g.G y i j) x)

def abstractGaussCurvature (g : RiemannianMetric2D) (x : Fin 2 → ℝ) : ℝ :=
  let Γ := abstractChristoffel g
  let R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k s =>
    scalarPartialDeriv k (fun y => Γ y i j s) x -
    scalarPartialDeriv j (fun y => Γ y i k s) x +
    ∑ t, (Γ x i j t * Γ x k t s - Γ x i k t * Γ x j t s)
  (∑ u, (g.G x) 1 u * R 0 0 1 u) / (g.G x).det

def IsDoublyPeriodic (g : RiemannianMetric2D) (T₁ T₂ : ℝ) : Prop :=
  (∀ x : Fin 2 → ℝ, g.G (![x 0 + T₁, x 1]) = g.G x) ∧
  (∀ x : Fin 2 → ℝ, g.G (![x 0, x 1 + T₂]) = g.G x)


def loweredChristoffel (g : RiemannianMetric2D) (i j k : Fin 2)
    (x : Fin 2 → ℝ) : ℝ :=
  (1/2) * (scalarPartialDeriv j (fun y => g.G y i k) x +
           scalarPartialDeriv i (fun y => g.G y j k) x -
           scalarPartialDeriv k (fun y => g.G y i j) x)

def connectionFormF₁ (g : RiemannianMetric2D) (x : Fin 2 → ℝ) : ℝ :=
  -(loweredChristoffel g 0 1 1 x) / Real.sqrt ((g.G x).det)

def connectionFormF₂ (g : RiemannianMetric2D) (x : Fin 2 → ℝ) : ℝ :=
  (loweredChristoffel g 0 0 1 x) / Real.sqrt ((g.G x).det)
