/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedTreeSelectorClose
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc28_rootedTreeArmSelection_of_rootedArmDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rfp_RootedArmDivergence ω n) :
    bas_RootedTreeArmSelection ω n := by
  obtain ⟨b, rank, hdata, hinj, hdiv⟩ := h
  refine ⟨b, (fun x y => rank x < rank y), hdata, ?_, ?_⟩
  · 
    intro x hxbox htri y hybox htriy hxy hconn
    have hne : rank x ≠ rank y := hinj x hxbox htri y hybox htriy hxy hconn
    rcases lt_trichotomy (rank x) (rank y) with hlt | heq | hgt
    · exact Or.inl hlt
    · exact absurd heq hne
    · exact Or.inr hgt
  · 
    intro x hxbox htri y hybox htriy hconn hlt
    have hxy : x ≠ y := by rintro rfl; exact lt_irrefl _ hlt
    exact hdiv x hxbox htri y hybox htriy hxy hconn hlt


theorem bc28_directionalDivergence_of_rootedArmDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rfp_RootedArmDivergence ω n) :
    fpc_DirectionalChosenArmDivergence ω n :=
  bas_directionalDivergence_of_rootedTreeArmSelection ω n
    (bc28_rootedTreeArmSelection_of_rootedArmDivergence ω n h)


theorem bc28_pairwiseCutSeparation_of_rootedArmDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rfp_RootedArmDivergence ω n) :
    fac_PairwiseCutSeparation ω n :=
  bas_pairwiseCutSeparation_of_rootedTreeArmSelection ω n
    (bc28_rootedTreeArmSelection_of_rootedArmDivergence ω n h)


theorem bc28_globalForestArms_of_rootedArmDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rfp_RootedArmDivergence ω n) :
    aed_GlobalForestArms ω n :=
  bas_globalForestArms_of_rootedTreeArmSelection ω n
    (bc28_rootedTreeArmSelection_of_rootedArmDivergence ω n h)


theorem bc28_Tcount_le_boundary_of_rootedArmDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : rfp_RootedArmDivergence ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bas_Tcount_le_boundary_of_rootedTreeArmSelection ω n hn
    (bc28_rootedTreeArmSelection_of_rootedArmDivergence ω n h)


theorem bc28_burton_keane_bernoulli_of_rootedArmDivergence (hd : 1 ≤ d) (p : NNReal)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      rfp_RootedArmDivergence ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bas_burton_keane_bernoulli_of_rootedTreeArmSelection hd p hp1 hp0
    (fun ω n hn => bc28_rootedTreeArmSelection_of_rootedArmDivergence ω n (hres ω n hn))
    htrif


theorem bc28_exists_depthRank (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∃ rank : Site d → ℕ ×ₗ ℕ,
      ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x ≠ rank y :=
  stt_exists_depthRank ω n


theorem bc28_rootedArmDivergence_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    rfp_RootedArmDivergence ω n :=
  rfp_rootedArmDivergence_of_noTrif ω n hno


theorem bc28_rootedArmDivergence_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdeep : ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) :
    rfp_RootedArmDivergence ω n :=
  rfp_rootedArmDivergence_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hdeep


theorem bc28_rootedArmDivergence_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w →
      (ly i w = 0 ↔ lx w ≠ i))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hcy : ∀ i, lx (b (y i)) = i)
    {j₀ : Fin 3} (hcx : lx (b x₀) = j₀)
    (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
    rfp_RootedArmDivergence ω n :=
  rfp_rootedArmDivergence_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
    hsingle b hbdata hcy hcx hcentral


theorem bc28_rootedTreeArmSelection_of_claw_via_divergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w →
      (ly i w = 0 ↔ lx w ≠ i))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hcy : ∀ i, lx (b (y i)) = i)
    {j₀ : Fin 3} (hcx : lx (b x₀) = j₀)
    (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
    bas_RootedTreeArmSelection ω n :=
  bc28_rootedTreeArmSelection_of_rootedArmDivergence ω n
    (bc28_rootedArmDivergence_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral)


end StatMech.Walls
