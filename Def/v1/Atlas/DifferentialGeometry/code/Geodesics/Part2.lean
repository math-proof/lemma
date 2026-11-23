/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Geodesics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds.Part6
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Manifolds
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Intrinsic
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part4
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite
public import Abbrev.v1.Atlas.DifferentialGeometry.code.GaussMap
public import Structure.v1.Atlas.DifferentialGeometry.code.Geodesics

@[expose] public section

open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators


noncomputable section

namespace Geodesics

def firstVariationEnergy {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) : ℝ :=
  deriv (fun s => energy (V.Γ s) a b) 0

def variationField {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) (t : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  deriv (fun s => V.Γ s t) 0

def IsEnergyMinimizer {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : Prop :=
  ∀ V : SmoothVariation M γ a b, ∀ s : ℝ, energy γ a b ≤ energy (V.Γ s) a b

def IsGeodesicOn {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (I : Set ℝ) : Prop :=
  ContDiff ℝ ⊤ γ ∧
  (∀ t ∈ I, γ t ∈ M) ∧
  (∀ t ∈ I, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    IsLocalDefiningFunction ψ M (γ t) →
    ∀ v ∈ Hypersurface.tangentSpace ψ (γ t), ⟪deriv (deriv γ) t, v⟫_ℝ = 0)

def SatisfiesGeodesicEquation {n : ℕ} (patch : HypersurfacePatch n)
    (c : ℝ → Fin n → ℝ) : Prop :=
  ContDiff ℝ ⊤ c ∧
  (∀ t, c t ∈ patch.domain) ∧
  (∀ t, ∀ k : Fin n,
    (deriv (deriv c) t) k +
      ∑ i : Fin n, ∑ j : Fin n,
        ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
          (deriv c t i) * (deriv c t j) = 0)

end Geodesics
end
