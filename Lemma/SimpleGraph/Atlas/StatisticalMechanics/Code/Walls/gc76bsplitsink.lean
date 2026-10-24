import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc76bsplitsink
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc76b_disjointConnectors_of_splitFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_disjointConnectors_of_splitFlow_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {o g : W}
-- given
  (hPG : P ⊆ K ∪ L)
  (hPsrc : sources ends P = ({o, g} : Finset W))
  (hPD : Disjoint P D)
  (hPconn : connK ends P o g) :
-- imply
  ∃ P', P' ⊆ K ∪ L ∧ sources ends P' = ({o, g} : Finset W) ∧ Disjoint P' D ∧ connK ends P' o g := by
-- proof
  apply StatMech.Walls.gc76b_disjointConnectors_of_splitFlow ends hPG hPsrc hPD hPconn

/--
[gc76b_survives_of_splitFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_survives_of_splitFlow_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L D P : Finset ι}
  {o g : W}
-- given
  (hPG : P ⊆ K ∪ L)
  (hPD : Disjoint P D)
  (hPconn : connK ends P o g) :
-- imply
  connK ends ((K ∪ L) \ D) o g := by
-- proof
  apply StatMech.Walls.gc76b_survives_of_splitFlow ends hPG hPD hPconn

/--
[gc76b_splitCut_card_ge2_of_flow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_splitCut_card_ge2_of_flow_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K L : Finset ι}
  {o y g : W}
  {P₁ P₂ : Finset ι}
  {C : Finset ι}
-- given
  (hP₁G : P₁ ⊆ K ∪ L)
  (hP₁conn : connK ends P₁ o g)
  (hP₂G : P₂ ⊆ K ∪ L)
  (hP₂conn : connK ends P₂ y g)
  (hdisj : Disjoint P₁ P₂)
  (hC : gc76b_IsSplitCut ends K L o y g C) :
-- imply
  2 ≤ #C := by
-- proof
  apply StatMech.Walls.gc76b_splitCut_card_ge2_of_flow ends hP₁G hP₁conn hP₂G hP₂conn hdisj hC

/--
[gc76b_ssEnds_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_loopless_eq :
-- imply
  ∀ i : Fin 5, ¬ (gc76b_ssEnds i).IsDiag := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_loopless

/--
[gc76b_ssEnds_univ_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_univ_sources_eq :
-- imply
  sources gc76b_ssEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_univ_sources

/--
[gc76b_ssEnds_K_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_K_sources_eq :
-- imply
  sources gc76b_ssEnds ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_K_sources

/--
[gc76b_ssEnds_g_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_g_deg3_eq :
-- imply
  degK gc76b_ssEnds (univ : Finset (Fin 5)) 3 = 3 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_g_deg3

/--
[gc76b_ssEnds_L23_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_L23_sources_eq :
-- imply
  sources gc76b_ssEnds ({2, 3} : Finset (Fin 5)) = (∅ : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_L23_sources

/--
[gc76b_ssEnds_gate_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_gate_23_eq :
-- imply
  connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_gate_23

/--
[gc76b_ssEnds_gate_24](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_gate_24_eq :
-- imply
  connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_gate_24

/--
[gc76b_ssEnds_gate_34](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_gate_34_eq :
-- imply
  connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_gate_34

/--
[gc76b_ssEnds_gate_fail_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_gate_fail_empty_eq :
-- imply
  ¬ connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ (∅ : Finset (Fin 5))) 1 3 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_gate_fail_empty

/--
[gc76b_ssEnds_sourceEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_sourceEmpty_eq :
-- imply
  ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter (fun L => sources gc76b_ssEnds L = (∅ : Finset (Fin 4))) = ({∅, {2, 3}, {2, 4}, {3, 4}} : Finset (Finset (Fin 5))) := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_sourceEmpty

/--
[gc76b_ssEnds_LblockSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_LblockSet_eq :
-- imply
  gc51_LblockSet gc76b_ssEnds ({0} : Finset (Fin 5)) 0 1 3 = ({({2, 3} : Finset (Fin 5)), ({2, 4} : Finset (Fin 5)), ({3, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_LblockSet

/--
[gc76b_ssEnds_og_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_og_23_eq :
-- imply
  connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_og_23

/--
[gc76b_ssEnds_split_og_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_split_og_23_eq :
-- imply
  ¬ connK gc76b_ssEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_split_og_23

/--
[gc76b_ssEnds_split_yg_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_split_yg_23_eq :
-- imply
  ¬ connK gc76b_ssEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 2 3 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_split_yg_23

/--
[gc76b_ss_splitCut1_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ss_splitCut1_23_eq :
-- imply
  gc76b_IsSplitCut gc76b_ssEnds ({0} : Finset (Fin 5)) ({2, 3} : Finset (Fin 5)) 0 2 3 ({0} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc76b_ss_splitCut1_23

/--
[gc76b_ssEnds_D_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ssEnds_D_data_eq :
-- imply
  ({1, 2} : Finset (Fin 5)) ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) ∧ sources gc76b_ssEnds ({1, 2} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4)) ∧ degK gc76b_ssEnds ({1, 2} : Finset (Fin 5)) 3 = 1 := by
-- proof
  apply StatMech.Walls.gc76b_ssEnds_D_data

/--
[gc76b_ss_residue_23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ss_residue_23_eq :
-- imply
  connK gc76b_ssEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc76b_ss_residue_23

/--
[gc76b_ss_residue_24](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ss_residue_24_eq :
-- imply
  connK gc76b_ssEnds ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc76b_ss_residue_24

/--
[gc76b_ss_residue_34](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ss_residue_34_eq :
-- imply
  connK gc76b_ssEnds ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc76b_ss_residue_34

/--
[gc76b_ss_splitSink_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ss_splitSink_refuted_eq :
-- imply
  gc76b_IsSplitCut gc76b_ssEnds ({0} : Finset (Fin 5)) ({2, 3} : Finset (Fin 5)) 0 2 3 ({0} : Finset (Fin 5)) ∧ #({0} : Finset (Fin 5)) = 1 ∧ connK gc76b_ssEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
-- proof
  apply StatMech.Walls.gc76b_ss_splitSink_refuted

/--
[gc76b_ss_cutEdge_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ss_cutEdge_in_K_eq :
-- imply
  (0 : Fin 5) ∈ ({0} : Finset (Fin 5)) ∧ (0 : Fin 5) ∉ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) ∧ ({1, 2} : Finset (Fin 5)) ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) := by
-- proof
  apply StatMech.Walls.gc76b_ss_cutEdge_in_K

/--
[gc76b_IrreducibleTwoCommodity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_IrreducibleTwoCommodity_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {o x y g : W}
  {D : Finset ι}
-- given
  (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  (∀ L ∈ gc51_LblockSet ends K o x g, ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) ↔ (∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) := by
-- proof
  apply StatMech.Walls.gc76b_IrreducibleTwoCommodity ends hnd K hog

/--
[gc76b_ss_twoCommodityLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_ss_twoCommodityLeaf_eq :
-- imply
  gc71_TwoCommodityLeaf gc76b_ssEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc76b_ss_twoCommodityLeaf

/--
[gc76b_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean)
-/
@[path]
private lemma gc76b_status_eq :
-- imply
  (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K L D P : Finset ι) (o g : W), P ⊆ K ∪ L → sources ends P = ({o, g} : Finset W) → Disjoint P D → connK ends P o g → ∃ P', P' ⊆ K ∪ L ∧ sources ends P' = ({o, g} : Finset W) ∧ Disjoint P' D ∧ connK ends P' o g) ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W] (ends : ι → Sym2 W) (K L : Finset ι) (o y g : W) (P₁ P₂ : Finset ι), P₁ ⊆ K ∪ L → connK ends P₁ o g → P₂ ⊆ K ∪ L → connK ends P₂ y g → Disjoint P₁ P₂ → ∀ C : Finset ι, gc76b_IsSplitCut ends K L o y g C → 2 ≤ #C) ∧ (gc76b_IsSplitCut gc76b_ssEnds ({0} : Finset (Fin 5)) ({2, 3} : Finset (Fin 5)) 0 2 3 ({0} : Finset (Fin 5)) ∧ #({0} : Finset (Fin 5)) = 1 ∧ connK gc76b_ssEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3) ∧ gc71_TwoCommodityLeaf gc76b_ssEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc76b_status


-- created on 2026-10-23
