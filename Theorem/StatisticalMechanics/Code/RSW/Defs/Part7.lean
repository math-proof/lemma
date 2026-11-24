module
public import Mathlib
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
public import Def.StatisticalMechanics.Code.RSW.Defs.Part7
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


theorem P5c.p5 {Ξ : Type*} {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
    (h : P5c μ) (ξ : Ξ) : P5 (μ ξ) := by
  intro α hα
  obtain ⟨c, hc, hbound⟩ := h α hα
  exact ⟨c, hc, fun n => (hbound ξ n).1⟩

end Box
end RSW
end StatMech
