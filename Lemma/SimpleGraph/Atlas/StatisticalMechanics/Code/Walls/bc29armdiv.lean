import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc29armdiv
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc29_notSameArm_of_armSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_notSameArm_of_armSplit_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y bx by' : Site d}
-- given
  (hy_bx : Connected d ω y bx)
  (hne_bx : y ≠ bx)
  (hy_by : Connected d ω y by')
  (hne_by : y ≠ by')
  (hsplit : ¬ Connected d (removeSite y ω) by' bx) :
-- imply
  ¬ fsp_sameArm ω y bx by' := by
-- proof
  apply StatMech.Walls.bc29_notSameArm_of_armSplit ω hy_bx hne_bx hy_by hne_by hsplit

/--
[bc29_armSplit_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_armSplit_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx by' : Site 1), ¬ Connected 1 (removeSite y ω) by' bx := by
-- proof
  apply StatMech.Walls.bc29_armSplit_consistent

/--
[bc29_multiAncestorSplit_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_multiAncestorSplit_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx₁ bx₂ by' : Site 1), ¬ Connected 1 (removeSite y ω) by' bx₁ ∧ ¬ Connected 1 (removeSite y ω) by' bx₂ := by
-- proof
  apply StatMech.Walls.bc29_multiAncestorSplit_consistent

/--
[bc29_armDivergenceForRank_of_rootedDownArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_armDivergenceForRank_of_rootedDownArmForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc29_RootedDownArmForest ω n rank) :
-- imply
  bc28_ArmDivergenceForRank ω n rank := by
-- proof
  apply StatMech.Walls.bc29_armDivergenceForRank_of_rootedDownArmForest ω n rank h

/--
[bc29_rootedArmDivergence_of_rootedDownArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_rootedArmDivergence_of_rootedDownArmForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc29_RootedDownArmForest ω n rank) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc29_rootedArmDivergence_of_rootedDownArmForest ω n rank hinj h

/--
[bc29_rootedArmDivergence_of_bundled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_rootedArmDivergence_of_bundled_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc29_BundledRootedDownArmForest ω n) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc29_rootedArmDivergence_of_bundled ω n h

/--
[bc29_rootedTreeArmSelection_of_bundled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_rootedTreeArmSelection_of_bundled_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc29_BundledRootedDownArmForest ω n) :
-- imply
  bas_RootedTreeArmSelection ω n := by
-- proof
  apply StatMech.Walls.bc29_rootedTreeArmSelection_of_bundled ω n h

/--
[bc29_Tcount_le_boundary_of_rootedDownArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_Tcount_le_boundary_of_rootedDownArmForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bc29_BundledRootedDownArmForest ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc29_Tcount_le_boundary_of_rootedDownArmForest ω n hn h

/--
[bc29_burton_keane_bernoulli_of_rootedDownArmForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_burton_keane_bernoulli_of_rootedDownArmForest_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc29_BundledRootedDownArmForest ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc29_burton_keane_bernoulli_of_rootedDownArmForest hd p hp1 hp0 hres htrif

/--
[bc29_rootedDownArmForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_rootedDownArmForest_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc29_rootedDownArmForest_of_noTrif ω n hno

/--
[bc29_rootedDownArmForest_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_rootedDownArmForest_of_threeChain_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g : Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hmbox : m ∈ box d n)
  (hgbox : g ∈ box d n)
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hmg : m ≠ g)
  (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
  (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc29_rootedDownArmForest_of_threeChain ω n b hx0box hmbox hgbox hx0m hx0g hmg hthree hbx0 hbm hbg hsxm hsxg hsmg

/--
[bc29_rootedDownArmForest_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean)
-/
@[path]
private lemma bc29_rootedDownArmForest_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b (y i))).Infinite)
  (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
  (hssib : ∀ i j : Fin 3, (j : ℕ) < i → ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc29_rootedDownArmForest_of_claw ω n x₀ y b hx0box hydata hyinj hsingle hbx0 hby hsx0 hssib


-- created on 2026-10-23
