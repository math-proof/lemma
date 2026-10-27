import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[fsp_singleCut_sep_of_distinctWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_singleCut_sep_of_distinctWitness_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a c bx by_ : Site d}
-- given
  (hdis : ¬ Connected d (removeSite x ω) a c)
  (hbx : bkfl_inArm ω x a bx)
  (hby : bkfl_inArm ω x c by_) :
-- imply
  ¬ Connected d (removeSite x ω) bx by_ := by
-- proof
  apply StatMech.Percolation.fsp_singleCut_sep_of_distinctWitness ω hdis hbx hby

/--
[fsp_treeSelector_iff_singleCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_treeSelector_iff_singleCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  fsp_TreeSelector ω n ↔ daep2_SingleCutBranchSeparation ω n := by
-- proof
  apply StatMech.Percolation.fsp_treeSelector_iff_singleCut ω n

/--
[fsp_singleCut_of_treeSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_singleCut_of_treeSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fsp_TreeSelector ω n) :
-- imply
  daep2_SingleCutBranchSeparation ω n := by
-- proof
  apply StatMech.Percolation.fsp_singleCut_of_treeSelector ω n h

/--
[fsp_singleCutSep_of_armPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_singleCutSep_of_armPlacement_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {b : Site d → Site d}
  {x y : Site d}
-- given
  (h : fsp_ArmPlacement ω b x y) :
-- imply
  ¬ Connected d (removeSite x ω) (b x) (b y) := by
-- proof
  apply StatMech.Percolation.fsp_singleCutSep_of_armPlacement ω b h

/--
[fsp_treeSelector_of_rootedArmOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_treeSelector_of_rootedArmOrder_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fsp_RootedArmOrder ω n) :
-- imply
  fsp_TreeSelector ω n := by
-- proof
  apply StatMech.Percolation.fsp_treeSelector_of_rootedArmOrder ω n h

/--
[fsp_singleCut_of_rootedArmOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_singleCut_of_rootedArmOrder_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fsp_RootedArmOrder ω n) :
-- imply
  daep2_SingleCutBranchSeparation ω n := by
-- proof
  apply StatMech.Percolation.fsp_singleCut_of_rootedArmOrder ω n h

/--
[fsp_inSomeArm_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_inSomeArm_of_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x v : Site d}
-- given
  (hxv : Connected d ω x v)
  (hne : x ≠ v) :
-- imply
  ∃ a, (openSubgraph d ω).Adj x a ∧ Connected d (removeSite x ω) a v := by
-- proof
  apply StatMech.Percolation.fsp_inSomeArm_of_connected ω hxv hne

/--
[fsp_armWitness_inArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_armWitness_inArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x v : Site d}
-- given
  (hxv : Connected d ω x v)
  (hne : x ≠ v) :
-- imply
  Connected d (removeSite x ω) (fsp_armWitness ω x v) v := by
-- proof
  apply StatMech.Percolation.fsp_armWitness_inArm ω hxv hne

/--
[fsp_armWitness_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_armWitness_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x v : Site d}
-- given
  (hxv : Connected d ω x v)
  (hne : x ≠ v) :
-- imply
  (openSubgraph d ω).Adj x (fsp_armWitness ω x v) := by
-- proof
  apply StatMech.Percolation.fsp_armWitness_adj ω hxv hne

/--
[fsp_sep_of_notSameArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_sep_of_notSameArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x u v : Site d}
-- given
  (hxu : Connected d ω x u)
  (hneu : x ≠ u)
  (hxv : Connected d ω x v)
  (hnev : x ≠ v)
  (hdiv : ¬ fsp_sameArm ω x u v) :
-- imply
  ¬ Connected d (removeSite x ω) u v := by
-- proof
  apply StatMech.Percolation.fsp_sep_of_notSameArm ω hxu hneu hxv hnev hdiv

/--
[fsp_armPlacement_of_divergentWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_armPlacement_of_divergentWitness_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {b : Site d → Site d}
  {x y a c : Site d}
-- given
  (hdis : ¬ Connected d (removeSite x ω) a c)
  (hbx : bkfl_inArm ω x a (b x))
  (hby : bkfl_inArm ω x c (b y)) :
-- imply
  fsp_ArmPlacement ω b x y := by
-- proof
  apply StatMech.Percolation.fsp_armPlacement_of_divergentWitness ω b hdis hbx hby

/--
[fsp_inArm_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_inArm_of_witness_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a v : Site d}
-- given
  (h : Connected d (removeSite x ω) a v) :
-- imply
  bkfl_inArm ω x a v := by
-- proof
  apply StatMech.Percolation.fsp_inArm_of_witness ω h

/--
[fsp_inArm_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_inArm_self_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a : Site d} :
-- imply
  bkfl_inArm ω x a a := by
-- proof
  apply StatMech.Percolation.fsp_inArm_self ω x a

/--
[fsp_armPlacement_of_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_armPlacement_of_divergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {b : Site d → Site d}
  {x y : Site d}
-- given
  (hbxx : b x ≠ x)
  (hbyx : x ≠ b y)
  (hxbx : Connected d ω x (b x))
  (hxby : Connected d ω x (b y))
  (hdiv : ¬ fsp_sameArm ω x (b x) (b y)) :
-- imply
  fsp_ArmPlacement ω b x y := by
-- proof
  apply StatMech.Percolation.fsp_armPlacement_of_divergence ω b hbxx hbyx hxbx hxby hdiv

/--
[fsp_rootedArmOrder_of_divergentArmOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_rootedArmOrder_of_divergentArmOrder_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fsp_DivergentArmOrder ω n) :
-- imply
  fsp_RootedArmOrder ω n := by
-- proof
  apply StatMech.Percolation.fsp_rootedArmOrder_of_divergentArmOrder ω n h

/--
[fsp_rootedArmOrder_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_rootedArmOrder_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  fsp_RootedArmOrder ω n := by
-- proof
  apply StatMech.Percolation.fsp_rootedArmOrder_of_noTrif ω n hno

/--
[fsp_rootedArmOrder_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_rootedArmOrder_of_uniqueTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ a : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (habox : a ∈ box d n)
  (haconn : Connected d ω x₀ a)
  (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
  (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
-- imply
  fsp_RootedArmOrder ω n := by
-- proof
  apply StatMech.Percolation.fsp_rootedArmOrder_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[fsp_rootedArmOrder_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_rootedArmOrder_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hdata_x : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hdata_y : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
  (hplace_xy : fsp_ArmPlacement ω b x₀ y₀)
  (hplace_yx : fsp_ArmPlacement ω b y₀ x₀) :
-- imply
  fsp_RootedArmOrder ω n := by
-- proof
  apply StatMech.Percolation.fsp_rootedArmOrder_of_twoTrif ω n b hx0y0 htwo hdata_x hdata_y hplace_xy hplace_yx

/--
[fsp_divergentArmOrder_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_divergentArmOrder_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hdata_x : b x₀ ∈ box d n ∧ b x₀ ≠ x₀ ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hdata_y : b y₀ ∈ box d n ∧ b y₀ ≠ y₀ ∧ Connected d ω y₀ (b y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
  (hdiv_xy : ¬ fsp_sameArm ω x₀ (b x₀) (b y₀))
  (hdiv_yx : ¬ fsp_sameArm ω y₀ (b y₀) (b x₀)) :
-- imply
  fsp_DivergentArmOrder ω n := by
-- proof
  apply StatMech.Percolation.fsp_divergentArmOrder_of_twoTrif ω n b hx0y0 htwo hdata_x hdata_y hdiv_xy hdiv_yx

/--
[fsp_Tcount_le_boundary_of_treeSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_Tcount_le_boundary_of_treeSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : fsp_TreeSelector ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.fsp_Tcount_le_boundary_of_treeSelector ω n hn h

/--
[fsp_Tcount_le_boundary_of_rootedArmOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_Tcount_le_boundary_of_rootedArmOrder_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : fsp_RootedArmOrder ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.fsp_Tcount_le_boundary_of_rootedArmOrder ω n hn h

/--
[fsp_burton_keane_bernoulli_of_treeSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_burton_keane_bernoulli_of_treeSelector_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_TreeSelector ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.fsp_burton_keane_bernoulli_of_treeSelector hd p hp1 hp0 hres htrif

/--
[fsp_burton_keane_bernoulli_of_rootedArmOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_burton_keane_bernoulli_of_rootedArmOrder_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_RootedArmOrder ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.fsp_burton_keane_bernoulli_of_rootedArmOrder hd p hp1 hp0 hres htrif

/--
[fsp_Tcount_le_boundary_of_divergentArmOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_Tcount_le_boundary_of_divergentArmOrder_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : fsp_DivergentArmOrder ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.fsp_Tcount_le_boundary_of_divergentArmOrder ω n hn h

/--
[fsp_burton_keane_bernoulli_of_divergentArmOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean)
-/
@[path]
private lemma fsp_burton_keane_bernoulli_of_divergentArmOrder_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_DivergentArmOrder ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.fsp_burton_keane_bernoulli_of_divergentArmOrder hd p hp1 hp0 hres htrif


-- created on 2026-10-23
