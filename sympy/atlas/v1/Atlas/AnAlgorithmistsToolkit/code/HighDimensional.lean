/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HighDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Body
open MeasureTheory

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped NNReal

namespace HighDimensional

def IsCLipschitz {α : Type*} {β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (c : ℝ) (f : α → β) : Prop :=
  ∀ u v : α, ‖f u - f v‖ ≤ c * ‖u - v‖

structure IsDEmbedding {X : Type*} [MetricSpace X] [Fintype X] {k : ℕ}
    (D : ℝ) (f : X → EuclideanSpace ℝ (Fin k)) : Prop where
  one_lipschitz : ∀ x y : X, ‖f x - f y‖ ≤ dist x y
  distortion_bound : ∀ x y : X, dist x y ≤ D * ‖f x - f y‖


abbrev UnitSphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

instance (n : ℕ) : MeasurableSpace (UnitSphere n) := inferInstance

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


end ChernoffHoeffding

open scoped InnerProductSpace
open Finset
