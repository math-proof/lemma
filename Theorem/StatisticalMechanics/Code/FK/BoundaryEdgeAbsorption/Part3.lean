/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Def.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part4
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (boundary : V -> Prop) [DecidablePred boundary]

section NestedBoundary

variable {Vin Vout : Type*} [DecidableEq Vin] [DecidableEq Vout]
  (Gin : SimpleGraph Vin) (Gout : SimpleGraph Vout)
  (incl : Vin → Vout)
  (bdryIn : Vin → Prop) (bdryOut : Vout → Prop)


theorem finiteWiredEventMass_mono {W : Type*} [Fintype W]
    [DecidableEq W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (bdry : W → Prop) [DecidablePred bdry]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {A B : Set (ConfigSpace (Sym2 W))} (hAB : A ⊆ B) :
    finiteWiredEventMass K bdry p q A ≤
      finiteWiredEventMass K bdry p q B := by
  unfold finiteWiredEventMass
  apply Finset.sum_le_sum
  intro omega _
  apply mul_le_mul_of_nonneg_right _
    (wiredFkProb_nonneg K bdry hp hp1 hq omega)
  by_cases hA : omega ∈ A
  · simp [Set.indicator_of_mem hA, Set.indicator_of_mem (hAB hA)]
  · by_cases hB : omega ∈ B <;> simp [hA, hB]


theorem ocd_boundaryReach_of_outerBoundaryReach
    (hadj : ocd_AdjMatch Gin Gout incl)
    (hmargin : ∀ x, ¬ bdryOut (incl x))
    (hcross : ∀ x c, Gout.Adj (incl x) c →
      c ∉ Set.range incl → bdryIn x)
    (rho : ConfigSpace (Sym2 Vout)) (root : Vin)
    (hreach : ∃ y, bdryOut y ∧
      (openSub Gout rho).Reachable (incl root) y) :
    ∃ z, bdryIn z ∧
      (openSub Gin (ocd_innerRestrict incl rho)).Reachable root z := by
  obtain ⟨y, hy, p⟩ := hreach
  obtain ⟨walk⟩ := p
  have go : ∀ {a y : Vout} (walk : (openSub Gout rho).Walk a y),
      ∀ x : Vin, a = incl x → bdryOut y →
        ∃ z, bdryIn z ∧
          (openSub Gin (ocd_innerRestrict incl rho)).Reachable x z := by
    intro a y walk
    induction walk with
    | nil =>
        intro x hax hy'
        exact (hmargin x (hax ▸ hy')).elim
    | @cons a b y hab walk ih =>
        intro x hax hy'
        subst a
        by_cases hx : bdryIn x
        · exact ⟨x, hx, .refl x⟩
        · by_cases hb : b ∈ Set.range incl
          · obtain ⟨w, rfl⟩ := hb
            have habIn : (openSub Gin
                (ocd_innerRestrict incl rho)).Adj x w := by
              rw [openSub_adj] at hab ⊢
              refine ⟨(hadj x w).2 hab.1, ?_⟩
              simpa [ocd_innerRestrict, ocd_innerEdge_mk] using hab.2
            obtain ⟨z, hz, hwz⟩ := ih w rfl hy'
            exact ⟨z, hz, habIn.reachable.trans hwz⟩
          · rw [openSub_adj] at hab
            exact ⟨x, hcross x b hab.1 hb, .refl x⟩
  exact go walk root rfl hy

theorem outerRootBoundaryEvent_subset_innerRestrict
    (hadj : ocd_AdjMatch Gin Gout incl)
    (hmargin : ∀ x, ¬ bdryOut (incl x))
    (hcross : ∀ x c, Gout.Adj (incl x) c →
      c ∉ Set.range incl → bdryIn x)
    (root : Vin) :
    finiteRootBoundaryEvent Gout bdryOut (incl root) ⊆
      ocd_innerRestrict incl ⁻¹'
        finiteRootBoundaryEvent Gin bdryIn root := by
  intro rho hrho
  exact ocd_boundaryReach_of_outerBoundaryReach Gin Gout incl bdryIn bdryOut
    hadj hmargin hcross rho root hrho

end NestedBoundary
end
end StatMech.FK
