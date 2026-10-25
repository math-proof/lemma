/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalAdaptivePairedConnectionEvent_condMass_le_boxConn
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i targetRow : Fin R.height) (psi : ConfigSpace (Sym2 R.Vertex))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (FKRectPrimalAdaptivePairedConnectionEvent
          R S i targetRow psi).indicator (fun _ => (1 : Real)) rho *
          FK.condBcProb (fkRectCutGraph R)
            (boundaryCliqueGraph (fun _ : R.Vertex => False)) p q
            (fkRectPrimalAdaptiveInsideEdges R S psi) psi rho) <=
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxConnEvent 2 (R.width + R.height)
            (fkRectVertexBoxEmbedding R (fkRectLeftColumn R, i))
            (fkRectVertexBoxEmbedding R
              (fkRectRightColumn R, targetRow))) := by
  by_cases hsource : FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i)
  · have hempty :
        FKRectPrimalAdaptivePairedConnectionEvent R S i targetRow psi = ∅ := by
      ext rho
      constructor
      · rintro ⟨hnot, _⟩
        exact (hnot hsource).elim
      · simp
    rw [hempty]
    simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
    exact measureReal_nonneg
  · by_cases htarget : FKRectPrimalFullExploredVertex R S psi
        (fkRectRightColumn R, targetRow)
    · have hempty :
          FKRectPrimalAdaptivePairedConnectionEvent R S i targetRow psi = ∅ := by
        ext rho
        constructor
        · rintro ⟨_, hnot, _⟩
          exact (hnot htarget).elim
        · simp
      rw [hempty]
      simp only [Set.indicator_empty, zero_mul, Finset.sum_const_zero]
      exact measureReal_nonneg
    · let eta := fkRectCutConfigOfFull R psi
      let source : FKRectPrimalUnexploredVertex R S eta.1 :=
        ⟨(fkRectLeftColumn R, i), fun h => hsource
          ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
      let target : FKRectPrimalUnexploredVertex R S eta.1 :=
        ⟨(fkRectRightColumn R, targetRow), fun h => htarget
          ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
      let A := FKRectPrimalUnexploredConnectionEvent R S eta.1 source target
      have hevent :
          FKRectPrimalAdaptivePairedConnectionEvent R S i targetRow psi =
            FK.ocd_innerRestrict
              (Subtype.val : FKRectPrimalUnexploredVertex R S eta.1 ->
                R.Vertex) ⁻¹' A := by
        ext rho
        constructor
        · rintro ⟨hsource', htarget', hconn⟩
          simpa only [eta, source, target, A] using hconn
        · intro hconn
          exact ⟨hsource, htarget, by
            simpa only [eta, source, target, A] using hconn⟩
      rw [hevent]
      rw [fkRectPrimalAdaptive_condMass_eq_freeUnexplored
        R S psi hp hp1 (zero_lt_one.trans_le hq) A]
      simpa only [A, source, target,
        fkRectPrimalUnexploredBoxEmbedding]
        using fkRectPrimalUnexploredConnection_freeMass_le_boxConn
          R S eta.1 source target hp hp1 hq


end
end StatMech.FrontierD
