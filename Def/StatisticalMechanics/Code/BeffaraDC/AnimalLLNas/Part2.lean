module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
public import Theorem.StatisticalMechanics.Code.BeffaraDC.AnimalLLNas
open MeasureTheory Filter Topology Finset
open StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace BeffaraDC

noncomputable def animalValue (ω : ℤ → ℝ) (n : ℕ) : ℝ :=
  (range (n + 1)).sup' (by simp) (fun a => ∑ i ∈ range a, ω (i : ℤ))


end BeffaraDC
end StatMech
