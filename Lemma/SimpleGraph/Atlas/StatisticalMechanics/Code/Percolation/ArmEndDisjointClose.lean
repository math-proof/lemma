import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[aed_globalCut_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_globalCut_equiv_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  Equivalence (Connected d (removeSites T ω)) := by
-- proof
  apply StatMech.Percolation.aed_globalCut_equiv T ω

/--
[aed_sameComponent_of_commonLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_sameComponent_of_commonLeaf_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v w : Site d}
-- given
  (hu : Connected d (removeSites T ω) u w)
  (hv : Connected d (removeSites T ω) v w) :
-- imply
  aed_sameGlobalComponent T ω u v := by
-- proof
  apply StatMech.Percolation.aed_sameComponent_of_commonLeaf T ω hu hv

/--
[aed_globalCutArmEnds_disjoint_of_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_globalCutArmEnds_disjoint_of_distinct_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {u v : Site d}
-- given
  (hdis : ¬ aed_sameGlobalComponent T ω u v) :
-- imply
  Disjoint (daep_globalCutArmEnds T ω n u) (daep_globalCutArmEnds T ω n v) := by
-- proof
  apply StatMech.Percolation.aed_globalCutArmEnds_disjoint_of_distinct T ω n hdis

/--
[aed_hall_of_distinctComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_hall_of_distinctComponents_eq
  {d : ℕ}
  {T' : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {T : Finset (Site d)}
  {b : Site d → Site d}
-- given
  (hne : ∀ x ∈ T, (daep_globalCutArmEnds T' ω n (b x)).Nonempty)
  (hdistinct : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ aed_sameGlobalComponent T' ω (b x) (b y)) :
-- imply
  ∀ S : Finset (Site d), S ⊆ T → S.card ≤ (S.biUnion (fun x => daep_globalCutArmEnds T' ω n (b x))).card := by
-- proof
  apply StatMech.Percolation.aed_hall_of_distinctComponents T' ω n T b hne hdistinct

/--
[aed_hallArmEnds_of_globalForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_hallArmEnds_of_globalForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : aed_GlobalForestArms ω n) :
-- imply
  bhs_HallArmEnds ω n := by
-- proof
  apply StatMech.Percolation.aed_hallArmEnds_of_globalForestArms ω n hn h

/--
[aed_globalForestArms_of_globalCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_globalForestArms_of_globalCutSeparation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daep_GlobalCutSeparation ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.aed_globalForestArms_of_globalCutSeparation ω n h

/--
[aed_globalCutSeparation_of_globalForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_globalCutSeparation_of_globalForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : aed_GlobalForestArms ω n) :
-- imply
  daep_GlobalCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.aed_globalCutSeparation_of_globalForestArms ω n h

/--
[aed_globalForestArms_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_globalForestArms_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.aed_globalForestArms_of_noTrif ω n hno

/--
[aed_globalForestArms_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_globalForestArms_of_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {b : Site d → Site d}
-- given
  (hexist : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hdistinct : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y)) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.aed_globalForestArms_of_disjoint ω n b hexist hdistinct

/--
[aed_globalForestArms_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_globalForestArms_of_uniqueTrif_eq
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
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.aed_globalForestArms_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[aed_Tcount_le_boundary_of_globalForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_Tcount_le_boundary_of_globalForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : aed_GlobalForestArms ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.aed_Tcount_le_boundary_of_globalForestArms ω n hn h

/--
[aed_burton_keane_bernoulli_of_globalForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_burton_keane_bernoulli_of_globalForestArms_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.aed_burton_keane_bernoulli_of_globalForestArms hd p hp1 hp0 hres htrif

/--
[aed_distinctComponent_iff_not_setoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_distinctComponent_iff_not_setoid_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d} :
-- imply
  ¬ aed_sameGlobalComponent T ω u v ↔ ¬ (aed_globalSetoid T ω).r u v := by
-- proof
  apply StatMech.Percolation.aed_distinctComponent_iff_not_setoid T ω u v

/--
[aed_hall_of_disjointLeaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_hall_of_disjointLeaves_eq
  {d : ℕ}
  {T' : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {T : Finset (Site d)}
  {b : Site d → Site d}
-- given
  (hne : ∀ x ∈ T, (daep_globalCutArmEnds T' ω n (b x)).Nonempty)
  (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (daep_globalCutArmEnds T' ω n (b x)) (daep_globalCutArmEnds T' ω n (b y))) :
-- imply
  ∀ S : Finset (Site d), S ⊆ T → S.card ≤ (S.biUnion (fun x => daep_globalCutArmEnds T' ω n (b x))).card := by
-- proof
  apply StatMech.Percolation.aed_hall_of_disjointLeaves T' ω n T b hne hdisj

/--
[aed_globalForestArms_of_forestPeel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean)
-/
@[path]
private lemma aed_globalForestArms_of_forestPeel_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bkfl_ForestPeel ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.aed_globalForestArms_of_forestPeel ω n h


-- created on 2026-10-23
