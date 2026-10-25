/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_liftSite_outgoingDart
    {L n : ℕ} [NeZero n] (v : Fin n → ons_Dart L) (k : Fin n) :
    (ons_liftSite v k, ons_liftDir v k) = v (-k) := rfl

theorem ons_liftSite_incomingRevDart
    {L n : ℕ} [NeZero n] (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (k : Fin n) :
    (ons_liftSite v k, ons_liftDir v (k - 1) + 2) =
      ons_dartRev L (v (-k + 1)) := by
  apply Prod.ext
  · exact hvalid (-k)
  · simp [ons_liftDir, ons_dartRev]
    congr 2
    abel


theorem ons_portEdge_mem_dartEdgeSet_at_liftSite_iff
    {L n : ℕ} [Fact (2 < L)] [NeZero n]
    (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hsite : Function.Injective (fun k ↦ (v k).1))
    (k : Fin n) (mu : Fin 4) :
    ons_portEdge L (ons_liftSite v k, mu) ∈ ons_dartEdgeSet v ↔
      mu = ons_liftDir v k ∨
        mu = ons_liftDir v (k - 1) + 2 := by
  constructor
  · intro hmem
    rw [ons_dartEdgeSet, Finset.mem_image] at hmem
    obtain ⟨j, -, hedge⟩ := hmem
    have hdarts := (ons_portEdge_eq_iff L
      (ons_liftSite v k, mu) (v j)).mp hedge
    rcases hdarts with hsame | hrev
    · left
      have hj : j = -k := hsite (by
        simpa [ons_liftSite] using congrArg Prod.fst hsame)
      subst j
      exact (congrArg Prod.snd hsame).symm
    · right
      have hsitej : (v (j - 1)).1 = ons_liftSite v k := by
        calc
          (v (j - 1)).1 =
              ons_dirStep L (v (j - 1 + 1)).2
                (v (j - 1 + 1)).1 := hvalid (j - 1)
          _ = ons_dirStep L (v j).2 (v j).1 := by congr 2 <;> abel
          _ = ons_dirStep L
              (ons_dartRev L (ons_liftSite v k, mu)).2
              (ons_dartRev L (ons_liftSite v k, mu)).1 := by
            rw [hrev]
          _ = ons_liftSite v k := by
            simp only [ons_dartRev]
            rw [ons_dirStep_opposite]
      have hj : j - 1 = -k := hsite hsitej
      have hj' : j = -k + 1 := by
        calc
          j = (j - 1) + 1 := by abel
          _ = -k + 1 := by rw [hj]
      have hdir := congrArg Prod.snd hrev
      simp only [ons_dartRev] at hdir
      rw [ons_liftDir]
      have hidx : -(k - 1) = j := by rw [hj']; abel
      rw [hidx]
      rw [hdir]
      fin_cases mu <;> rfl
  · intro hmu
    rw [ons_dartEdgeSet, Finset.mem_image]
    rcases hmu with rfl | rfl
    · refine ⟨-k, Finset.mem_univ _, ?_⟩
      rfl
    · refine ⟨-(k - 1), Finset.mem_univ _, ?_⟩
      rw [show -(k - 1) = -k + 1 by abel]
      rw [← ons_portEdge_rev L (v (-k + 1))]
      congr 1
      exact (ons_liftSite_incomingRevDart v hvalid k).symm

theorem ons_zeroFluxPotential_horizontal_boundary_of_zeroHomology
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
    (hhom : ons_evenHomology L F = 0)
    (p : ZMod L × ZMod L) :
    ons_zeroFluxPotential F p +
      ons_zeroFluxPotential F (p.1, p.2 - 1) =
        ons_horizontalZBit F p := by
  have hx : ons_xFlux F (-1) = 0 := by
    rw [← ons_evenHomology_fst_cast_eq_xFlux L F, hhom]
    rfl
  simpa [ons_zeroFluxHorizontal, hx] using
    ons_zeroFluxPotential_horizontal_boundary L F hF p

theorem ons_zeroFluxPotential_vertical_boundary_of_zeroHomology
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L))
    (hhom : ons_evenHomology L F = 0)
    (p : ZMod L × ZMod L) :
    ons_zeroFluxPotential F p +
      ons_zeroFluxPotential F (p.1 - 1, p.2) =
        ons_verticalZBit F p := by
  have hy : ons_yFlux F (-1) = 0 := by
    rw [← ons_evenHomology_snd_cast_eq_yFlux L F, hhom]
    rfl
  simpa [ons_zeroFluxVertical, hy] using
    ons_zeroFluxPotential_vertical_boundary L F hF p

end StatMech.Onsager
