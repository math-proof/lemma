import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafDisjointClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[fld_separate_of_outward_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_separate_of_outward_far_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y a a' : Site d}
-- given
  (hxT : x ∈ tfc_trifFinset ω n)
  (hyT : y ∈ tfc_trifFinset ω n)
  (hxy : x ≠ y)
  (haout : ∀ z ∈ tfc_trifFinset ω n, z ≠ x → ¬ Connected d (removeSite x ω) a z)
  (hfar : Connected d (removeSite x ω) a' y) :
-- imply
  ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) a a' := by
-- proof
  apply StatMech.Percolation.fld_separate_of_outward_far ω n hxT hyT hxy haout hfar

/--
[fld_outwardArm_of_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_outwardArm_of_forestPeel_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bkfl_ForestPeel ω n) :
-- imply
  fld_OutwardArm ω n := by
-- proof
  apply StatMech.Percolation.fld_outwardArm_of_forestPeel ω n h

/--
[fld_forestPeel_of_outwardArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_forestPeel_of_outwardArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fld_OutwardArm ω n) :
-- imply
  bkfl_ForestPeel ω n := by
-- proof
  apply StatMech.Percolation.fld_forestPeel_of_outwardArm ω n h

/--
[fld_outwardArm_iff_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_outwardArm_iff_forestPeel_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  fld_OutwardArm ω n ↔ bkfl_ForestPeel ω n := by
-- proof
  apply StatMech.Percolation.fld_outwardArm_iff_forestPeel ω n

/--
[fld_globalForestArms_of_outwardArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_globalForestArms_of_outwardArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fld_OutwardArm ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.fld_globalForestArms_of_outwardArm ω n h

/--
[fld_armEnds_disjoint_of_outward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_armEnds_disjoint_of_outward_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y a a' : Site d}
-- given
  (hxT : x ∈ tfc_trifFinset ω n)
  (hyT : y ∈ tfc_trifFinset ω n)
  (hxy : x ≠ y)
  (haout : ∀ z ∈ tfc_trifFinset ω n, z ≠ x → ¬ Connected d (removeSite x ω) a z)
  (hfar : Connected d (removeSite x ω) a' y) :
-- imply
  Disjoint (daep_globalCutArmEnds (tfc_trifFinset ω n) ω n a) (daep_globalCutArmEnds (tfc_trifFinset ω n) ω n a') := by
-- proof
  apply StatMech.Percolation.fld_armEnds_disjoint_of_outward ω n hxT hyT hxy haout hfar

/--
[fld_Tcount_le_boundary_of_outwardArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_Tcount_le_boundary_of_outwardArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : fld_OutwardArm ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.fld_Tcount_le_boundary_of_outwardArm ω n hn h

/--
[fld_burton_keane_bernoulli_of_outwardArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_burton_keane_bernoulli_of_outwardArm_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fld_OutwardArm ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.fld_burton_keane_bernoulli_of_outwardArm hd p hp1 hp0 hres htrif

/--
[fld_outwardArm_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_outwardArm_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  fld_OutwardArm ω n := by
-- proof
  apply StatMech.Percolation.fld_outwardArm_of_noTrif ω n hno

/--
[fld_outwardArm_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_outwardArm_of_uniqueTrif_eq
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
  fld_OutwardArm ω n := by
-- proof
  apply StatMech.Percolation.fld_outwardArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[fld_outwardArm_of_distinctClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_outwardArm_of_distinctClusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {arm : Site d → Site d}
-- given
  (hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → arm x ∈ box d n ∧ Connected d ω x (arm x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (arm x)).Infinite)
  (hfar : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ z ∈ tfc_trifFinset ω n, z ≠ x → Connected d (removeSite z ω) (arm x) x)
  (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
-- imply
  fld_OutwardArm ω n := by
-- proof
  apply StatMech.Percolation.fld_outwardArm_of_distinctClusters ω n arm hdata hfar hsep

/--
[fld_outwardArm_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafDisjointClose.lean)
-/
@[path]
private lemma fld_outwardArm_of_twoTrif_eq
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
  fld_OutwardArm ω n := by
-- proof
  apply StatMech.Percolation.fld_outwardArm_of_twoTrif ω n arm hx0y0 htwo hdata_x hdata_y hocc_x hocc_y hfar_x hfar_y


-- created on 2026-10-23
