/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPositiveSeamDisagreements_nonempty
    (T : EvenTorus) (omega eta : SixVertexArrows T) (n : Nat)
    (homega : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (heta : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (sixVertexPositiveSeamDisagreements T omega eta).Nonempty := by
  classical
  let A : Finset (Fin T.width) :=
    Finset.univ.filter fun i => omega.vertical (i, svFinLast T.height_pos)
  let B : Finset (Fin T.width) :=
    Finset.univ.filter fun i => eta.vertical (i, svFinLast T.height_pos)
  have hA : A.card = n - 1 := by
    simpa [A, sixVertexUpCount, svTorusVerticalRows] using homega
  have hB : B.card = n + 1 := by
    simpa [B, sixVertexUpCount, svTorusVerticalRows] using heta
  have hcard : A.card < B.card := by omega
  obtain ⟨i, hiB, hiA⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hetaTrue : eta.vertical (i, svFinLast T.height_pos) = true := by
    simpa [B] using hiB
  have homegaFalse : omega.vertical (i, svFinLast T.height_pos) = false := by
    cases h : omega.vertical (i, svFinLast T.height_pos)
    · rfl
    · exact False.elim (hiA (by simp [A, h]))
  exact ⟨i, by
    simp [sixVertexPositiveSeamDisagreements, homegaFalse, hetaTrue]⟩


end
end StatMech.FrontierD
