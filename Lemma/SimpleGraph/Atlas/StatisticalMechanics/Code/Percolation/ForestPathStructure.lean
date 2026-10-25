import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ForestPathStructure.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[fps_cutX_sep_of_privateFar_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_cutX_sep_of_privateFar_x_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x bx by_ y : Site d}
-- given
  (hpriv : ¬ Connected d (removeSite x ω) bx y)
  (hfar : Connected d (removeSite x ω) by_ y) :
-- imply
  ¬ Connected d (removeSite x ω) bx by_ := by
-- proof
  apply StatMech.Percolation.fps_cutX_sep_of_privateFar_x ω hpriv hfar

/--
[fps_cutY_sep_of_privateFar_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_cutY_sep_of_privateFar_y_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y bx by_ x : Site d}
-- given
  (hpriv : ¬ Connected d (removeSite y ω) by_ x)
  (hfar : Connected d (removeSite y ω) bx x) :
-- imply
  ¬ Connected d (removeSite y ω) bx by_ := by
-- proof
  apply StatMech.Percolation.fps_cutY_sep_of_privateFar_y ω hpriv hfar

/--
[fps_eitherCut_sep_of_twoSidedPrivateFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_eitherCut_sep_of_twoSidedPrivateFar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y bx by_ : Site d}
-- given
  (hprivx : ¬ Connected d (removeSite x ω) bx y)
  (hprivy : ¬ Connected d (removeSite y ω) by_ x)
  (hfar : Connected d (removeSite x ω) by_ y ∨ Connected d (removeSite y ω) bx x) :
-- imply
  ¬ Connected d (removeSite x ω) bx by_ ∨ ¬ Connected d (removeSite y ω) bx by_ := by
-- proof
  apply StatMech.Percolation.fps_eitherCut_sep_of_twoSidedPrivateFar ω hprivx hprivy hfar

/--
[fps_pairwiseCutSeparation_of_twoSidedPrivateFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_pairwiseCutSeparation_of_twoSidedPrivateFar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fps_TwoSidedPrivateFar ω n) :
-- imply
  fac_PairwiseCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fps_pairwiseCutSeparation_of_twoSidedPrivateFar ω n h

/--
[fps_globalForestArms_of_twoSidedPrivateFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_globalForestArms_of_twoSidedPrivateFar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fps_TwoSidedPrivateFar ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.fps_globalForestArms_of_twoSidedPrivateFar ω n h

/--
[fps_twoSidedPrivateFar_of_privateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_twoSidedPrivateFar_of_privateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daepf_PrivateArm ω n) :
-- imply
  fps_TwoSidedPrivateFar ω n := by
-- proof
  apply StatMech.Percolation.fps_twoSidedPrivateFar_of_privateArm ω n h

/--
[fps_globalForestArms_of_privateArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_globalForestArms_of_privateArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : daepf_PrivateArm ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Percolation.fps_globalForestArms_of_privateArm ω n h

/--
[fps_eitherCut_sep_via_farY_only](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_eitherCut_sep_via_farY_only_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y bx by_ : Site d}
-- given
  (hprivy : ¬ Connected d (removeSite y ω) by_ x)
  (hfary : Connected d (removeSite y ω) bx x) :
-- imply
  ¬ Connected d (removeSite y ω) bx by_ := by
-- proof
  apply StatMech.Percolation.fps_eitherCut_sep_via_farY_only ω hprivy hfary

/--
[fps_twoSidedPrivateFar_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_twoSidedPrivateFar_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  fps_TwoSidedPrivateFar ω n := by
-- proof
  apply StatMech.Percolation.fps_twoSidedPrivateFar_of_noTrif ω n hno

/--
[fps_twoSidedPrivateFar_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_twoSidedPrivateFar_of_uniqueTrif_eq
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
  fps_TwoSidedPrivateFar ω n := by
-- proof
  apply StatMech.Percolation.fps_twoSidedPrivateFar_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[fps_twoSidedPrivateFar_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_twoSidedPrivateFar_of_twoTrif_eq
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
  (hpriv_yx : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀)
  (hfar_xy : Connected d (removeSite x₀ ω) (b y₀) y₀)
  (hfar_yx : Connected d (removeSite y₀ ω) (b x₀) x₀) :
-- imply
  fps_TwoSidedPrivateFar ω n := by
-- proof
  apply StatMech.Percolation.fps_twoSidedPrivateFar_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hpriv_xy hpriv_yx hfar_xy hfar_yx

/--
[fps_claw_satisfies_pairwiseCutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_claw_satisfies_pairwiseCutSeparation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {lx : Site d → Fin 3}
  {ly : Fin 3 → Site d → Fin 3}
  {b : Site d → Site d}
  {j₀ : Fin 3}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v → (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w → (ly i w = 0 ↔ lx w ≠ i))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcy : ∀ i, lx (b (y i)) = i)
  (hcx : lx (b x₀) = j₀)
  (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
-- imply
  fac_PairwiseCutSeparation ω n := by
-- proof
  apply StatMech.Percolation.fps_claw_satisfies_pairwiseCutSeparation ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[fps_Tcount_le_boundary_of_twoSidedPrivateFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_Tcount_le_boundary_of_twoSidedPrivateFar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : fps_TwoSidedPrivateFar ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.fps_Tcount_le_boundary_of_twoSidedPrivateFar ω n hn h

/--
[fps_burton_keane_bernoulli_of_twoSidedPrivateFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean)
-/
@[path]
private lemma fps_burton_keane_bernoulli_of_twoSidedPrivateFar_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fps_TwoSidedPrivateFar ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.fps_burton_keane_bernoulli_of_twoSidedPrivateFar hd p hp1 hp0 hres htrif


-- created on 2026-10-23
