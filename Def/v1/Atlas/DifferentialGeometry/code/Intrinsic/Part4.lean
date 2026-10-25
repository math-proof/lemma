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
import Structure.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part2


noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

namespace AbstractGaussBonnet

open MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

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

end AbstractGaussBonnet
end ChristoffelSymbols
end
