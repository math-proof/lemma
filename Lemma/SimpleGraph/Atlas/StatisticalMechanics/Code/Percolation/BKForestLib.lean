import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bkfl_inArm_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_inArm_self_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a : Site d} :
-- imply
  bkfl_inArm ω x a a := by
-- proof
  apply StatMech.Percolation.bkfl_inArm_self ω x a

/--
[bkfl_inArm_symm_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_inArm_symm_witness_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a a' v : Site d}
-- given
  (haa' : Connected d (removeSite x ω) a a')
  (h : bkfl_inArm ω x a v) :
-- imply
  bkfl_inArm ω x a' v := by
-- proof
  apply StatMech.Percolation.bkfl_inArm_symm_witness ω haa' h

/--
[bkfl_sameArm_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_sameArm_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a u v : Site d}
-- given
  (hu : bkfl_inArm ω x a u)
  (hv : bkfl_inArm ω x a v) :
-- imply
  Connected d (removeSite x ω) u v := by
-- proof
  apply StatMech.Percolation.bkfl_sameArm_connected ω hu hv

/--
[bkfl_arms_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_arms_separate_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a b u w : Site d}
-- given
  (hdis : ¬ Connected d (removeSite x ω) a b)
  (hu : bkfl_inArm ω x a u)
  (hw : bkfl_inArm ω x b w) :
-- imply
  ¬ Connected d (removeSite x ω) u w := by
-- proof
  apply StatMech.Percolation.bkfl_arms_separate ω hdis hu hw

/--
[bkfl_atMostOneArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_atMostOneArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ v : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  ¬ (bkfl_inArm ω x a₁ v ∧ bkfl_inArm ω x a₂ v) ∧ ¬ (bkfl_inArm ω x a₁ v ∧ bkfl_inArm ω x a₃ v) ∧ ¬ (bkfl_inArm ω x a₂ v ∧ bkfl_inArm ω x a₃ v) := by
-- proof
  apply StatMech.Percolation.bkfl_atMostOneArm ω hd12 hd13 hd23

/--
[bkfl_singleCut_sep_of_privateFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_singleCut_sep_of_privateFar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {b : Site d → Site d}
  {x y : Site d}
-- given
  (h : bkfl_PrivateFar ω b x y) :
-- imply
  ¬ Connected d (removeSite x ω) (b x) (b y) := by
-- proof
  apply StatMech.Percolation.bkfl_singleCut_sep_of_privateFar ω b h

/--
[bkfl_privateArm_of_coherentSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_privateArm_of_coherentSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bkfl_CoherentArmSelector ω n) :
-- imply
  daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Percolation.bkfl_privateArm_of_coherentSelector ω n h

/--
[bkfl_singleCutBranchSeparation_of_coherentSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_singleCutBranchSeparation_of_coherentSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bkfl_CoherentArmSelector ω n) :
-- imply
  daep2_SingleCutBranchSeparation ω n := by
-- proof
  apply StatMech.Percolation.bkfl_singleCutBranchSeparation_of_coherentSelector ω n h

/--
[bkfl_Tcount_le_boundary_of_coherentSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_Tcount_le_boundary_of_coherentSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bkfl_CoherentArmSelector ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.bkfl_Tcount_le_boundary_of_coherentSelector ω n hn h

/--
[bkfl_coherentSelector_of_existsPrivateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_coherentSelector_of_existsPrivateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bkfl_ExistsPrivateArm ω n) :
-- imply
  bkfl_CoherentArmSelector ω n := by
-- proof
  apply StatMech.Percolation.bkfl_coherentSelector_of_existsPrivateArm ω n h

/--
[bkfl_privateArm_of_existsPrivateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_privateArm_of_existsPrivateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bkfl_ExistsPrivateArm ω n) :
-- imply
  daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Percolation.bkfl_privateArm_of_existsPrivateArm ω n h

/--
[bkfl_Tcount_le_boundary_of_existsPrivateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_Tcount_le_boundary_of_existsPrivateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bkfl_ExistsPrivateArm ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.bkfl_Tcount_le_boundary_of_existsPrivateArm ω n hn h

/--
[bkfl_trif_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_trif_branches_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (htri : IsTrifurcation d ω x) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (Connected d ω x a₁ ∧ Connected d ω x a₂ ∧ Connected d ω x a₃) ∧ (¬ Connected d (removeSite x ω) a₁ a₂ ∧ ¬ Connected d (removeSite x ω) a₁ a₃ ∧ ¬ Connected d (removeSite x ω) a₂ a₃) := by
-- proof
  apply StatMech.Percolation.bkfl_trif_branches ω htri

/--
[bkfl_vertex_meets_atMostOne_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_vertex_meets_atMostOne_arm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ v : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  (bkfl_inArm ω x a₁ v → ¬ bkfl_inArm ω x a₂ v ∧ ¬ bkfl_inArm ω x a₃ v) ∧ (bkfl_inArm ω x a₂ v → ¬ bkfl_inArm ω x a₁ v ∧ ¬ bkfl_inArm ω x a₃ v) ∧ (bkfl_inArm ω x a₃ v → ¬ bkfl_inArm ω x a₁ v ∧ ¬ bkfl_inArm ω x a₂ v) := by
-- proof
  apply StatMech.Percolation.bkfl_vertex_meets_atMostOne_arm ω hd12 hd13 hd23

/--
[bkfl_pointwise_of_freeArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_pointwise_of_freeArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {T : Finset (Site d)}
  {x a : Site d}
-- given
  (hdata : a ∈ box d n ∧ Connected d ω x a ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite)
  (hfree : ∀ y ∈ T, y ≠ x → ¬ Connected d (removeSite x ω) a y)
  (hfar : ∀ z ∈ T, z ≠ x → Connected d (removeSite z ω) a x) :
-- imply
  bkfl_PointwisePrivateFar ω n T x a := by
-- proof
  apply StatMech.Percolation.bkfl_pointwise_of_freeArm ω n T hdata hfree hfar

/--
[bkfl_free_of_unoccupied](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_free_of_unoccupied_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : Finset (Site d)}
  {x a : Site d}
-- given
  (h : ¬ bkfl_Occupied ω T x a) :
-- imply
  ∀ y ∈ T, y ≠ x → ¬ Connected d (removeSite x ω) a y := by
-- proof
  apply StatMech.Percolation.bkfl_free_of_unoccupied ω T h

/--
[bkfl_pointwise_of_unoccupiedArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_pointwise_of_unoccupiedArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {T : Finset (Site d)}
  {x a : Site d}
-- given
  (hdata : a ∈ box d n ∧ Connected d ω x a ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite)
  (hunocc : ¬ bkfl_Occupied ω T x a)
  (hfar : ∀ z ∈ T, z ≠ x → Connected d (removeSite z ω) a x) :
-- imply
  bkfl_PointwisePrivateFar ω n T x a := by
-- proof
  apply StatMech.Percolation.bkfl_pointwise_of_unoccupiedArm ω n T hdata hunocc hfar

/--
[bkfl_exists_unoccupied_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_exists_unoccupied_arm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : Finset (Site d)}
  {x a₁ a₂ a₃ : Site d}
-- given
  (hsome : ¬ bkfl_Occupied ω T x a₁ ∨ ¬ bkfl_Occupied ω T x a₂ ∨ ¬ bkfl_Occupied ω T x a₃) :
-- imply
  ∃ a ∈ ({a₁, a₂, a₃} : Finset (Site d)), ¬ bkfl_Occupied ω T x a := by
-- proof
  apply StatMech.Percolation.bkfl_exists_unoccupied_arm ω T hsome

/--
[bkfl_sameArm_occupants_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_sameArm_occupants_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a y y' : Site d}
-- given
  (hy : Connected d (removeSite x ω) a y)
  (hy' : Connected d (removeSite x ω) a y') :
-- imply
  Connected d (removeSite x ω) y y' := by
-- proof
  apply StatMech.Percolation.bkfl_sameArm_occupants_connected ω hy hy'

/--
[bkfl_existsPrivateArm_of_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_existsPrivateArm_of_forestPeel_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bkfl_ForestPeel ω n) :
-- imply
  bkfl_ExistsPrivateArm ω n := by
-- proof
  apply StatMech.Percolation.bkfl_existsPrivateArm_of_forestPeel ω n h

/--
[bkfl_privateArm_of_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_privateArm_of_forestPeel_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bkfl_ForestPeel ω n) :
-- imply
  daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Percolation.bkfl_privateArm_of_forestPeel ω n h

/--
[bkfl_Tcount_le_boundary_of_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_Tcount_le_boundary_of_forestPeel_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bkfl_ForestPeel ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.bkfl_Tcount_le_boundary_of_forestPeel ω n hn h

/--
[bkfl_forestPeel_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_forestPeel_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bkfl_ForestPeel ω n := by
-- proof
  apply StatMech.Percolation.bkfl_forestPeel_of_noTrif ω n hno

/--
[bkfl_forestPeel_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_forestPeel_of_uniqueTrif_eq
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
  bkfl_ForestPeel ω n := by
-- proof
  apply StatMech.Percolation.bkfl_forestPeel_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[bkfl_forestPeel_of_distinctClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_forestPeel_of_distinctClusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {arm : Site d → Site d}
-- given
  (hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → arm x ∈ box d n ∧ Connected d ω x (arm x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x)).Infinite)
  (hfar : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) (arm x) x)
  (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
-- imply
  bkfl_ForestPeel ω n := by
-- proof
  apply StatMech.Percolation.bkfl_forestPeel_of_distinctClusters ω n arm hdata hfar hsep

/--
[bkfl_forestPeel_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_forestPeel_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {arm : Site d → Site d}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hdata_x : arm x₀ ∈ box d n ∧ Connected d ω x₀ (arm x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x₀)).Infinite)
  (hdata_y : arm y₀ ∈ box d n ∧ Connected d ω y₀ (arm y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm y₀)).Infinite)
  (hocc_x : ¬ Connected d (removeSite x₀ ω) (arm x₀) y₀)
  (hocc_y : ¬ Connected d (removeSite y₀ ω) (arm y₀) x₀)
  (hfar_x : Connected d (removeSite y₀ ω) (arm x₀) x₀)
  (hfar_y : Connected d (removeSite x₀ ω) (arm y₀) y₀) :
-- imply
  bkfl_ForestPeel ω n := by
-- proof
  apply StatMech.Percolation.bkfl_forestPeel_of_twoTrif ω n arm hx0y0 htwo hdata_x hdata_y hocc_x hocc_y hfar_x hfar_y

/--
[bkfl_burton_keane_bernoulli_of_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean)
-/
@[path]
private lemma bkfl_burton_keane_bernoulli_of_forestPeel_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bkfl_ForestPeel ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.bkfl_burton_keane_bernoulli_of_forestPeel hd p hp1 hp0 hres htrif


-- created on 2026-10-23
