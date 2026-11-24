module
public import Theorem.StatisticalMechanics.Code.Percolation.Sharpness.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
public import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional
open MeasureTheory Set Filter Finset SimpleGraph
open scoped NNReal ENNReal Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def lineWord (hd : 0 < d) : ℕ → Fin d × Bool := fun _ => (⟨0, hd⟩, true)


end Percolation
end StatMech
