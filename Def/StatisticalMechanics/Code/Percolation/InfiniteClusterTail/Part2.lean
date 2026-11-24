module
public import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
public import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.InfiniteClusterTail
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

def tailComponentSites (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    Set (Site d) := Subtype.val '' (D : Set (tailClusterVertex omega x))

end StatMech.Percolation
