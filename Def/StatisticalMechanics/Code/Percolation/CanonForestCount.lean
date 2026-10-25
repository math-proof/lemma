/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Instance.StatisticalMechanics.Code.Percolation.CanonForestCount
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


noncomputable def cfc_emb (d n : ℕ) : (↑(box d (n + 1)) : Type) ↪ Site d :=
  ⟨Subtype.val, Subtype.val_injective⟩


noncomputable def cfc_Gbox (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (↑(box d (n + 1)) : Type) :=
  (openSubgraph d ω).induce (box d (n + 1))


noncomputable def cfc_F (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (↑(box d (n + 1)) : Type) :=
  osf_spanForest (cfc_Gbox ω n)


noncomputable def cfc_T (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : SimpleGraph (Site d) :=
  (cfc_F ω n).map (cfc_emb d n)


end Percolation
end StatMech
