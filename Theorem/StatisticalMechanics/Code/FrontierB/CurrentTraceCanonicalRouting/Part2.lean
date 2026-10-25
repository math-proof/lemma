/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceClusterUniqueness
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Def.StatisticalMechanics.Code.FrontierB.CurrentTraceCanonicalRouting
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation

open Percolation.DisjointPaths

variable {d : ℕ}


theorem not_mengerCore_of_originNeighborsCutConnected
    (ω : ConfigSpace (Sym2 (Site d)))
    (hconn : OriginNeighborsCutConnected ω) :
    ¬ MengerCore ω := by
  rintro ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, _hne, hadj,
    ⟨hcor₁, hcor₂, _hcor₃⟩, _hinf, ⟨hd12, _hd13, _hd23⟩⟩
  let ϱ := removeSite (0 : Site d) (forceOpenFinset G ω)
  have hle : removeSite (0 : Site d) ω ≤ ϱ := by
    intro e
    by_cases hzero : (0 : Site d) ∈ e
    · simp [ϱ, removeSite, hzero]
    · simp only [ϱ, removeSite, hzero, if_false]
      exact forceOpenFinset_le G ω e
  have ha12 : Connected d ϱ a₁ a₂ :=
    connected_mono hle (hconn a₁ a₂ hadj.1 hadj.2.1)
  have haw₁ : Connected d ϱ a₁ w₁ :=
    connected_removeSite_forceOpen_of_corridor ω G hcor₁
  have haw₂ : Connected d ϱ a₂ w₂ :=
    connected_removeSite_forceOpen_of_corridor ω G hcor₂
  have hw12 : Connected d ϱ w₁ w₂ := haw₁.symm.trans (ha12.trans haw₂)
  exact hd12 (cluster_eq_of_connected hw12)


end StatMech.FrontierB
