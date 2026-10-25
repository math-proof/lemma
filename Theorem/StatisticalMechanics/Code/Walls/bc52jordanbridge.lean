/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc52jordanbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc51armforest.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc52_spanForest_acyclic {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (osf_spanForest G).IsAcyclic :=
  osf_spanForest_acyclic G


theorem bc52_subgraph_acyclic {V : Type*} [Fintype V] (G T : SimpleGraph V)
    (hsub : T ≤ osf_spanForest G) : T.IsAcyclic :=
  (osf_spanForest_acyclic G).anti hsub


end StatMech.Walls
