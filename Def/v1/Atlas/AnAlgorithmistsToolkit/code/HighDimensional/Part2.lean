/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HighDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Convex.Body
public import Instance.v1.Atlas.AnAlgorithmistsToolkit.code.HighDimensional

@[expose] public section

open MeasureTheory

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped NNReal


namespace HighDimensional

noncomputable def sphereMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

noncomputable def uniformSphereMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (sphereMeasure n Set.univ)⁻¹ • sphereMeasure n

def IsMedian {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (M : ℝ) : Prop :=
  μ {x | f x ≤ M} ≥ μ Set.univ / 2 ∧ μ {x | f x ≥ M} ≥ μ Set.univ / 2

noncomputable def projFirstK (n k : ℕ) (hk : k ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => x (Fin.castLE hk i))

noncomputable def normProjFirstK (n k : ℕ) (hk : k ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖projFirstK n k hk x‖

noncomputable def sphereProjNorm (n k : ℕ) (hk : k ≤ n) :
    UnitSphere n → ℝ :=
  fun x => normProjFirstK n k hk (x : EuclideanSpace ℝ (Fin n))


def IsBoundedUnitInterval (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Measurable X ∧ ∀ᵐ ω ∂μ, 0 ≤ X ω ∧ X ω ≤ 1


end HighDimensional
