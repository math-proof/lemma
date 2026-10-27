import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc28forestroot.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc28_rootedTreeArmSelection_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_rootedTreeArmSelection_of_rootedArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  bas_RootedTreeArmSelection ω n := by
-- proof
  apply StatMech.Walls.bc28_rootedTreeArmSelection_of_rootedArmDivergence ω n h

/--
[bc28_directionalDivergence_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_directionalDivergence_of_rootedArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  fpc_DirectionalChosenArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc28_directionalDivergence_of_rootedArmDivergence ω n h

/--
[bc28_pairwiseCutSeparation_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_pairwiseCutSeparation_of_rootedArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  fac_PairwiseCutSeparation ω n := by
-- proof
  apply StatMech.Walls.bc28_pairwiseCutSeparation_of_rootedArmDivergence ω n h

/--
[bc28_globalForestArms_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_globalForestArms_of_rootedArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Walls.bc28_globalForestArms_of_rootedArmDivergence ω n h

/--
[bc28_Tcount_le_boundary_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_Tcount_le_boundary_of_rootedArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc28_Tcount_le_boundary_of_rootedArmDivergence ω n hn h

/--
[bc28_burton_keane_bernoulli_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_burton_keane_bernoulli_of_rootedArmDivergence_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → rfp_RootedArmDivergence ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc28_burton_keane_bernoulli_of_rootedArmDivergence hd p hp1 hp0 hres htrif

/--
[bc28_exists_depthRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_exists_depthRank_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∃ rank : Site d → ℕ ×ₗ ℕ, ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y := by
-- proof
  apply StatMech.Walls.bc28_exists_depthRank ω n

/--
[bc28_rootedArmDivergence_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_rootedArmDivergence_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc28_rootedArmDivergence_of_noTrif ω n hno

/--
[bc28_rootedArmDivergence_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_rootedArmDivergence_of_twoTrif_eq
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
  (hdeep : ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc28_rootedArmDivergence_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hdeep

/--
[bc28_rootedArmDivergence_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_rootedArmDivergence_of_claw_eq
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
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w → (ly i w = 0 ↔ lx w ≠ i))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcy : ∀ i, lx (b (y i)) = i)
  (hcx : lx (b x₀) = j₀)
  (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc28_rootedArmDivergence_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[bc28_rootedTreeArmSelection_of_claw_via_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_rootedTreeArmSelection_of_claw_via_divergence_eq
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
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w → (ly i w = 0 ↔ lx w ≠ i))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcy : ∀ i, lx (b (y i)) = i)
  (hcx : lx (b x₀) = j₀)
  (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
-- imply
  bas_RootedTreeArmSelection ω n := by
-- proof
  apply StatMech.Walls.bc28_rootedTreeArmSelection_of_claw_via_divergence ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[bc28_rootedArmDivergence_of_armDivergenceForRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_rootedArmDivergence_of_armDivergenceForRank_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc28_ArmDivergenceForRank ω n rank) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc28_rootedArmDivergence_of_armDivergenceForRank ω n rank hinj h

/--
[bc28_armDivergenceForRank_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_armDivergenceForRank_of_rootedArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  ∃ rank : Site d → ℕ ×ₗ ℕ, (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧ bc28_ArmDivergenceForRank ω n rank := by
-- proof
  apply StatMech.Walls.bc28_armDivergenceForRank_of_rootedArmDivergence ω n h

/--
[bc28_rootedArmDivergence_iff_existsRankDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_rootedArmDivergence_iff_existsRankDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  rfp_RootedArmDivergence ω n ↔ ∃ rank : Site d → ℕ ×ₗ ℕ, (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧ bc28_ArmDivergenceForRank ω n rank := by
-- proof
  apply StatMech.Walls.bc28_rootedArmDivergence_iff_existsRankDivergence ω n

/--
[bc28_armDivergenceForRank_of_threeTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_armDivergenceForRank_of_threeTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g : Site d}
  {b : Site d → Site d}
-- given
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hmg : m ≠ g)
  (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
  (hdxm : ¬ fsp_sameArm ω m (b x₀) (b m))
  (hdxg : ¬ fsp_sameArm ω g (b x₀) (b g))
  (hdmg : ¬ fsp_sameArm ω g (b m) (b g)) :
-- imply
  bc28_ArmDivergenceForRank ω n (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc28_armDivergenceForRank_of_threeTrif ω n b hx0m hx0g hmg hthree hbx0 hbm hbg hdxm hdxg hdmg

/--
[bc28_armDivergenceForRank_satisfiable_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc28forestroot.lean)
-/
@[path]
private lemma bc28_armDivergenceForRank_satisfiable_of_claw_eq
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
  (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v → (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
  (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w → (ly i w = 0 ↔ lx w ≠ i))
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hcy : ∀ i, lx (b (y i)) = i)
  (hcx : lx (b x₀) = j₀)
  (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
-- imply
  ∃ rank : Site d → ℕ ×ₗ ℕ, (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ z, z ∈ box d n → IsTrifurcation d ω z → x ≠ z → Connected d ω x z → rank x ≠ rank z) ∧ bc28_ArmDivergenceForRank ω n rank := by
-- proof
  apply StatMech.Walls.bc28_armDivergenceForRank_satisfiable_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar hsingle b hbdata hcy hcx hcentral


-- created on 2026-10-23
