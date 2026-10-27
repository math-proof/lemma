import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc26_arms_globalCut_pairwise_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_arms_globalCut_pairwise_disconnected_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hxT : x ∈ T)
  (htri : IsTrifurcation d ω x) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (Connected d ω x a₁ ∧ Connected d ω x a₂ ∧ Connected d ω x a₃) ∧ ((cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite) ∧ (¬ Connected d (removeSites T ω) a₁ a₂ ∧ ¬ Connected d (removeSites T ω) a₁ a₃ ∧ ¬ Connected d (removeSites T ω) a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc26_arms_globalCut_pairwise_disconnected T ω hxT htri

/--
[bc26_two_arms_avoid_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_two_arms_avoid_vertex_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ : Site d}
  {y : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  (¬ Connected d (removeSite x ω) a₁ y ∧ ¬ Connected d (removeSite x ω) a₂ y) ∨ (¬ Connected d (removeSite x ω) a₁ y ∧ ¬ Connected d (removeSite x ω) a₃ y) ∨ (¬ Connected d (removeSite x ω) a₂ y ∧ ¬ Connected d (removeSite x ω) a₃ y) := by
-- proof
  apply StatMech.Walls.bc26_two_arms_avoid_vertex ω hd12 hd13 hd23 y

/--
[bc26_avoiding_arm_of_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_avoiding_arm_of_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {y : Site d}
-- given
  (htri : IsTrifurcation d ω x) :
-- imply
  ∃ a : Site d, Connected d ω x a ∧ (cluster d ω a).Infinite ∧ ¬ bkfl_inArm ω x a y := by
-- proof
  apply StatMech.Walls.bc26_avoiding_arm_of_trif ω htri y

/--
[bc26_globalForestArms_of_globalCutArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_globalForestArms_of_globalCutArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc26_GlobalCutArmData ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Walls.bc26_globalForestArms_of_globalCutArmData ω n h

/--
[bc26_Tcount_le_boundary_of_globalCutArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_Tcount_le_boundary_of_globalCutArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bc26_GlobalCutArmData ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc26_Tcount_le_boundary_of_globalCutArmData ω n hn h

/--
[bc26_privateFarOrder_iff_coherentSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_privateFarOrder_iff_coherentSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc26_PrivateFarOrder ω n ↔ bkfl_CoherentArmSelector ω n := by
-- proof
  apply StatMech.Walls.bc26_privateFarOrder_iff_coherentSelector ω n

/--
[bc26_privateArm_of_privateFarOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_privateArm_of_privateFarOrder_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc26_PrivateFarOrder ω n) :
-- imply
  daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Walls.bc26_privateArm_of_privateFarOrder ω n h

/--
[bc26_count_of_privateFarOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_count_of_privateFarOrder_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bc26_PrivateFarOrder ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc26_count_of_privateFarOrder ω n hn h

/--
[bc26_burton_keane_bernoulli_of_privateFarOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_burton_keane_bernoulli_of_privateFarOrder_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc26_PrivateFarOrder ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc26_burton_keane_bernoulli_of_privateFarOrder hd p hp1 hp0 hres htrif

/--
[bc26_coarseTrif_arms_cutInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_coarseTrif_arms_cutInfinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : IsCoarseTrifurcation d 0 ω) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (Connected d ω (0 : Site d) a₁ ∧ Connected d ω (0 : Site d) a₂ ∧ Connected d ω (0 : Site d) a₃) ∧ ((cluster d (removeSite (0 : Site d) ω) a₁).Infinite ∧ (cluster d (removeSite (0 : Site d) ω) a₂).Infinite ∧ (cluster d (removeSite (0 : Site d) ω) a₃).Infinite) ∧ (¬ Connected d (removeSite (0 : Site d) ω) a₁ a₂ ∧ ¬ Connected d (removeSite (0 : Site d) ω) a₁ a₃ ∧ ¬ Connected d (removeSite (0 : Site d) ω) a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc26_coarseTrif_arms_cutInfinite h

/--
[bc26_globalForestArms_of_uniqueTrif_cutArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_globalForestArms_of_uniqueTrif_cutArm_eq
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
  apply StatMech.Walls.bc26_globalForestArms_of_uniqueTrif_cutArm ω n hx0box htri0 habox haconn hainf huniq

/--
[bc26_privateFarOrder_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_privateFarOrder_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc26_PrivateFarOrder ω n := by
-- proof
  apply StatMech.Walls.bc26_privateFarOrder_of_noTrif ω n hno

/--
[bc26_privateFarOrder_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_privateFarOrder_of_uniqueTrif_eq
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
  bc26_PrivateFarOrder ω n := by
-- proof
  apply StatMech.Walls.bc26_privateFarOrder_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[bc26_privateFarOrder_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean)
-/
@[path]
private lemma bc26_privateFarOrder_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hdata_x : bkfl_ArmData ω n b x₀)
  (hdata_y : bkfl_ArmData ω n b y₀)
  (hpf_xy : bkfl_PrivateFar ω b x₀ y₀)
  (hpf_yx : bkfl_PrivateFar ω b y₀ x₀) :
-- imply
  bc26_PrivateFarOrder ω n := by
-- proof
  apply StatMech.Walls.bc26_privateFarOrder_of_twoTrif ω n b hx0y0 htwo hdata_x hdata_y hpf_xy hpf_yx


-- created on 2026-10-23
