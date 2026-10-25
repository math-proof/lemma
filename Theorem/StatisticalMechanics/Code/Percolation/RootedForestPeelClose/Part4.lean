/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ForestAcyclicityClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.FacPairwiseClose
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedTreeSelectorClose
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
import Def.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem rfp_rootedSingleCutSeparation_of_armDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rfp_RootedArmDivergence ω n) :
    fcc_RootedSingleCutSeparation ω n := by
  obtain ⟨b, rank, hbdata, hrank, hdiv⟩ := h
  refine ⟨b, rank, hbdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hbxnotin : b x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata x hxbox htri).2.2
  have hbynotin : b y ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata y hybox htriy).2.2
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hbdata x hxbox htri).2.1
  have hy_by : Connected d ω y (b y) := (hbdata y hybox htriy).2.1
  exact fsp_sep_of_notSameArm ω hy_bx hne_y_bx hy_by hne_y_by
    (hdiv x hxbox htri y hybox htriy hxy hconn hlt)


theorem rfp_rootedArmDivergence_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    rfp_RootedArmDivergence ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)


theorem rfp_rootedArmDivergence_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdeep : ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) :
    rfp_RootedArmDivergence ω n := by
  classical
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro x hxbox htri x' hx'box htri' hxx' _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
    · rcases htwo x' hx'box htri' with rfl | rfl
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
      · exact absurd rfl hxx'
  · intro x hxbox htri x' hx'box htri' hxx' _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · exact hdeep
    · rcases htwo x' hx'box htri' with rfl | rfl
      · simp only [if_neg hx0y0, if_pos] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxx'


theorem rfp_rootedArmDivergence_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    rfp_RootedArmDivergence ω n := by
  
  obtain ⟨b', rank, hbdata', hrank, hsep⟩ :=
    fcc_rootedSingleCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral
  refine ⟨b', rank, hbdata', hrank, ?_⟩
  intro x hxbox htri y' hy'box htriy' hxy hconn hlt
  
  have hy'T : y' ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hy'box, htriy'⟩
  have hbxnotin : b' x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata' x hxbox htri).2.2
  have hbynotin : b' y' ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata' y' hy'box htriy').2.2
  have hne_y_bx : y' ≠ b' x := fun heq => hbxnotin (heq ▸ hy'T)
  have hne_y_by : y' ≠ b' y' := fun heq => hbynotin (heq ▸ hy'T)
  have hy_bx : Connected d ω y' (b' x) := hconn.symm.trans (hbdata' x hxbox htri).2.1
  have hy_by : Connected d ω y' (b' y') := (hbdata' y' hy'box htriy').2.1
  exact fcc_notSameArm_of_singleCut ω hy_bx hne_y_bx hy_by hne_y_by
    (hsep x hxbox htri y' hy'box htriy' hxy hconn hlt)


theorem rfp_rootedSpanningForest_of_coverArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hdiv : rfp_RootedArmDivergence ω n) :
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_coverSep ω n hcov
    (rfp_rootedSingleCutSeparation_of_armDivergence ω n hdiv)


theorem rfp_Tcount_le_boundary_of_coverArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hcov : fcc_ThreeArmCover ω n) (hdiv : rfp_RootedArmDivergence ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  stt_Tcount_le_boundary_of_rootedSpanningForest ω n hn
    (rfp_rootedSpanningForest_of_coverArmDivergence ω n hcov hdiv)


theorem rfp_burton_keane_bernoulli_of_coverArmDivergence (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hcov : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_ThreeArmCover ω n)
    (hdiv : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → rfp_RootedArmDivergence ω n)
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
  stt_burton_keane_bernoulli_of_rootedSpanningForest hd p hp1 hp0
    (fun ω n hn => rfp_rootedSpanningForest_of_coverArmDivergence ω n (hcov ω n hn) (hdiv ω n hn))
    htrif

end Percolation
end StatMech
