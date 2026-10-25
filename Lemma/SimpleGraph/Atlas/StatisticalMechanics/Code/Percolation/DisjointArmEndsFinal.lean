import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[daepf_shared_arm_reconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_shared_arm_reconnects_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a b v : Site d}
-- given
  (hva : Connected d (removeSite x ω) a v)
  (hvb : Connected d (removeSite x ω) b v) :
-- imply
  Connected d (removeSite x ω) a b := by
-- proof
  apply StatMech.Percolation.daepf_shared_arm_reconnects ω hva hvb

/--
[daepf_no_common_arm_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_no_common_arm_vertex_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a b : Site d}
-- given
  (hdis : ¬ Connected d (removeSite x ω) a b) :
-- imply
  ∀ v, ¬ (Connected d (removeSite x ω) a v ∧ Connected d (removeSite x ω) b v) := by
-- proof
  apply StatMech.Percolation.daepf_no_common_arm_vertex ω hdis

/--
[daepf_arm_class_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_arm_class_unique_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ : Site d}
  {v : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧ ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧ ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) := by
-- proof
  apply StatMech.Percolation.daepf_arm_class_unique ω hd12 hd13 hd23 v

/--
[daepf_in_some_or_no_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_in_some_or_no_arm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a₁ a₂ a₃ : Site d}
  {v : Site d}
-- given
  (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
  (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
  (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
-- imply
  (Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨ (Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨ (Connected d (removeSite x ω) a₃ v ∧ ¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨ (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) := by
-- proof
  apply StatMech.Percolation.daepf_in_some_or_no_arm ω hd12 hd13 hd23 v

/--
[daepf_singleCutBranchSeparation_of_privateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_singleCutBranchSeparation_of_privateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daepf_PrivateArm ω n) :
-- imply
  daep2_SingleCutBranchSeparation ω n := by
-- proof
  apply StatMech.Percolation.daepf_singleCutBranchSeparation_of_privateArm ω n h

/--
[daepf_privateArm_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_privateArm_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Percolation.daepf_privateArm_of_noTrif ω n hno

/--
[daepf_privateArm_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_privateArm_of_uniqueTrif_eq
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
  daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Percolation.daepf_privateArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[daepf_privateArm_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_privateArm_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
  (hpriv_xy : ¬ Connected d (removeSite x₀ ω) (b x₀) y₀)
  (hfar_xy : Connected d (removeSite x₀ ω) (b y₀) y₀)
  (hpriv_yx : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀)
  (hfar_yx : Connected d (removeSite y₀ ω) (b x₀) x₀) :
-- imply
  daepf_PrivateArm ω n := by
-- proof
  apply StatMech.Percolation.daepf_privateArm_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hpriv_xy hfar_xy hpriv_yx hfar_yx

/--
[daepf_Tcount_le_boundary_of_privateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_Tcount_le_boundary_of_privateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : daepf_PrivateArm ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.daepf_Tcount_le_boundary_of_privateArm ω n hn h

/--
[daepf_burton_keane_bernoulli_of_privateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsFinal.lean)
-/
@[path]
private lemma daepf_burton_keane_bernoulli_of_privateArm_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → daepf_PrivateArm ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.daepf_burton_keane_bernoulli_of_privateArm hd p hp1 hp0 hres htrif


-- created on 2026-10-23
