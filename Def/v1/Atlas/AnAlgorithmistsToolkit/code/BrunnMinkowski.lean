/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/BrunnMinkowski.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.ConvexGeometry.Part2
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.ConvexGeometry

@[expose] public section

open Pointwise


namespace BrunnMinkowski

def minkowskiSum {α : Type*} [Add α] (A B : Set α) : Set α := A + B

open MeasureTheory Set

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

variable (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant]

def bodyOfRevolution (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ × E) :=
  {p | p.1 ∈ s ∧ ‖p.2‖ ≤ f p.1}

def slice {E : Type*} (K : Set (ℝ × E)) (t : ℝ) : Set E :=
  {x | (t, x) ∈ K}


end BrunnsTheorem

open Real

noncomputable def centroid (K : Set (Fin (n + 1) → ℝ)) : Fin (n + 1) → ℝ :=
  ((volume K).toReal)⁻¹ • ∫ x in K, x ∂volume

def closedHalfspace (f : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | f x ≤ c}

namespace IsoperimetricInequality

open MeasureTheory Metric Set Real Pointwise

noncomputable def modulusOfConvexity (ε : ℝ) : ℝ :=
  1 - Real.sqrt (1 - ε ^ 2 / 4)


end IsoperimetricInequality

namespace GrunbaumConeReplacement

open MeasureTheory Set

noncomputable def volumeRatio {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (K L : Set α) : ENNReal :=
  μ (K ∩ L) / μ K

def posHalfSpace (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0}

end GrunbaumConeReplacement
