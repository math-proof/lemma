module
public import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.PivotalFactorFull.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite
open MeasureTheory Set Finset
open scoped NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def shk_firstExitSupport (S Lam : Finset (Site d)) :
    Finset (Sym2 (Site d)) :=
  (internalEdgesFinset S ∪
      (boundaryEdges d S).image (fun q => s(q.1, q.2))) ∪
    internalEdgesFinset Lam


end Sharpness
end StatMech
