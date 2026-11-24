module
public import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
public import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
public import Abbrev.StatisticalMechanics.Code.Percolation.InfiniteClusterTail
open Set
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Percolation

variable {d : ℕ}

noncomputable def tailClusterCut (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (K : Finset (Site d)) : Finset (tailClusterVertex omega x) :=
  K.preimage Subtype.val Subtype.val_injective.injOn


end StatMech.Percolation
