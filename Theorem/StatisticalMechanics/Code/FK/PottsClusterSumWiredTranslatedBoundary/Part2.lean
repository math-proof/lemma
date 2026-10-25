/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part2
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

theorem wiredConnToBdryMass_equiv
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (bdryV : V -> Prop) [DecidablePred bdryV]
    (bdryW : W -> Prop) [DecidablePred bdryW]
    (sigma : V ≃ W)
    (hadj : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (hbdry : ∀ x, bdryV x ↔ bdryW (sigma x))
    (p q : Real) (x : V) :
    wiredConnToBdryMass H bdryW p q (sigma x) =
      wiredConnToBdryMass G bdryV p q x := by
  classical
  unfold wiredConnToBdryMass
  rw [← Equiv.sum_comp (reCfgIsoEquiv sigma)]
  apply Finset.sum_congr rfl
  intro omega _
  have hconn :
      ConnToBdry G bdryV (reCfgIso sigma omega) x ↔
        ConnToBdry H bdryW omega (sigma x) := by
    constructor
    · rintro ⟨y, hy, hxy⟩
      refine ⟨sigma y, (hbdry y).mp hy, ?_⟩
      exact (fvs_openSubIso G H sigma hadj omega).reachable_iff.mpr hxy
    · rintro ⟨y, hy, hxy⟩
      refine ⟨sigma.symm y, ?_, ?_⟩
      · simpa using (hbdry (sigma.symm y)).mpr (by simpa using hy)
      · have hout : (openSub H omega).Reachable
            ((fvs_openSubIso G H sigma hadj omega) x)
            ((fvs_openSubIso G H sigma hadj omega) (sigma.symm y)) := by
          simpa [fvs_openSubIso] using hxy
        exact (fvs_openSubIso G H sigma hadj omega).reachable_iff.mp hout
  rw [show (finiteConnToBdryEvent H bdryW (sigma x)).indicator
      (fun _ => (1 : Real)) omega =
      (finiteConnToBdryEvent G bdryV x).indicator
        (fun _ => (1 : Real)) (reCfgIso sigma omega) by
    by_cases h : ConnToBdry G bdryV (reCfgIso sigma omega) x
    · rw [Set.indicator_of_mem
          (show omega ∈ finiteConnToBdryEvent H bdryW (sigma x) from hconn.mp h),
        Set.indicator_of_mem
          (show reCfgIso sigma omega ∈ finiteConnToBdryEvent G bdryV x from h)]
    · rw [Set.indicator_of_notMem
          (show omega ∉ finiteConnToBdryEvent H bdryW (sigma x) from
            fun ht => h (hconn.mpr ht)),
        Set.indicator_of_notMem
          (show reCfgIso sigma omega ∉ finiteConnToBdryEvent G bdryV x from h)]]
  rw [← fvs_wiredFkProb_reCfgIso G H bdryV bdryW sigma hadj hbdry]
  rfl


theorem connToBdry_innerRestrict_of_connToBdry_outer
    {d : Nat} {Sin Sout : Set (Site d)} [Fintype Sin] [Fintype Sout]
    (hsub : Sin ⊆ Sout)
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : Sin, ¬ bdryOut (flc_incl hsub x))
    (hbdryIn : ∀ (x : Sin) (z : Site d),
      NearestNeighbour d (x : Site d) z -> z ∉ Sin -> bdryIn x)
    (rho : ConfigSpace (Sym2 Sout)) (x : Sin)
    (hout : ConnToBdry
      (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut rho
        (flc_incl hsub x)) :
    ConnToBdry (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn
      (ocd_innerRestrict (flc_incl hsub) rho) x := by
  let Gout : SimpleGraph Sout :=
    SimpleGraph.comap Subtype.val (hypercubicLattice d)
  let Gin : SimpleGraph Sin :=
    SimpleGraph.comap Subtype.val (hypercubicLattice d)
  let OS := openSub Gout rho
  let os := openSub Gin (ocd_innerRestrict (flc_incl hsub) rho)
  obtain ⟨z, hzbdry, hxz⟩ := hout
  have hzout : (z : Site d) ∉ Sin := by
    intro hz
    let zin : Sin := ⟨z, hz⟩
    have heq : flc_incl hsub zin = z := Subtype.ext rfl
    exact hmargin zin (heq ▸ hzbdry)
  change OS.Reachable (flc_incl hsub x) z at hxz
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxz
  suffices H : ∀ w : Sout,
      Relation.ReflTransGen OS.Adj (flc_incl hsub x) w ->
        (ConnToBdry Gin bdryIn (ocd_innerRestrict (flc_incl hsub) rho) x ∨
          ∃ y : Sin, flc_incl hsub y = w ∧ os.Reachable x y) by
    rcases H z hxz with hdone | ⟨y, hy, hxy⟩
    · exact hdone
    · exact absurd (hy ▸ y.2) hzout
  intro w hw
  induction hw with
  | refl =>
      exact Or.inr ⟨x, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail u w huw hadj ih =>
      rcases ih with hdone | ⟨y, hy, hxy⟩
      · exact Or.inl hdone
      · subst hy
        by_cases hwIn : (w : Site d) ∈ Sin
        · let win : Sin := ⟨w, hwIn⟩
          have hwEq : flc_incl hsub win = w := Subtype.ext rfl
          refine Or.inr ⟨win, hwEq, hxy.trans ?_⟩
          apply SimpleGraph.Adj.reachable
          rw [openSub_adj] at hadj ⊢
          constructor
          · simpa [Gin, Gout, flc_incl] using hadj.1
          · simpa [ocd_innerRestrict, ocd_innerEdge, hwEq] using hadj.2
        · left
          refine ⟨y, hbdryIn y (w : Site d) ?_ hwIn, hxy⟩
          rw [openSub_adj] at hadj
          simpa [Gout, flc_incl] using hadj.1


theorem wiredConnToBdryMass_outer_le_inner
    {d : Nat} {Sin Sout : Set (Site d)} [Fintype Sin] [Fintype Sout]
    (hsub : Sin ⊆ Sout)
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : Sin, ¬ bdryOut (flc_incl hsub x))
    (hbdryIn : ∀ (x : Sin) (z : Site d),
      NearestNeighbour d (x : Site d) z -> z ∉ Sin -> bdryIn x)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : Sin) :
    wiredConnToBdryMass
        (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q
          (flc_incl hsub x) ≤
      wiredConnToBdryMass
        (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q x := by
  let Gout : SimpleGraph Sout :=
    SimpleGraph.comap Subtype.val (hypercubicLattice d)
  let Gin : SimpleGraph Sin :=
    SimpleGraph.comap Subtype.val (hypercubicLattice d)
  let A := finiteConnToBdryEvent Gin bdryIn x
  have hdom := ocd_latticeWired_inner_dominated
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    bdryOut bdryIn hmargin hbdryIn hp hp1 hq
    (finiteConnToBdryEvent_isIncreasing Gin bdryIn x)
  change (∑ rho,
      (finiteConnToBdryEvent Gout bdryOut (flc_incl hsub x)).indicator
          (fun _ => (1 : Real)) rho * wiredFkProb Gout bdryOut p q rho) ≤ _
  refine le_trans ?_ hdom
  apply Finset.sum_le_sum
  intro rho _
  apply mul_le_mul_of_nonneg_right _
    (wiredFkProb_nonneg Gout bdryOut hp hp1 (zero_lt_one.trans_le hq) rho)
  apply Set.indicator_le_indicator_of_subset
  · intro eta heta
    exact connToBdry_innerRestrict_of_connToBdry_outer hsub bdryOut bdryIn
      hmargin hbdryIn eta x heta
  · exact zero_le_one


end
end StatMech.FK
