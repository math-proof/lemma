module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.Theta
public import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.TildeBc.Part5
open MeasureTheory
open scoped BigOperators NNReal
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising

variable {d : ℕ}


noncomputable def phiIsing (d : ℕ) (β : ℝ) (S : Finset (Site d)) : ℝ :=
  Real.tanh β * ∑ e ∈ Percolation.boundaryEdges d S, corrOriginInner d β S e.1


end Sharpness
end StatMech
