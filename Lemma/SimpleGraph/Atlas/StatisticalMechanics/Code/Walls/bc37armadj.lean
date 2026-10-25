import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc37_selfDownArm_of_downArmSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_selfDownArm_of_downArmSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc37_DownArmSelector ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc37_selfDownArm_of_downArmSelector ω n h

/--
[bc37_rootedArmDivergence_of_downArmSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_rootedArmDivergence_of_downArmSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc37_DownArmSelector ω n) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc37_rootedArmDivergence_of_downArmSelector ω n h

/--
[bc37_armAdjacent_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armAdjacent_symm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (h : bc37_ArmAdjacent ω n x y) :
-- imply
  bc37_ArmAdjacent ω n y x := by
-- proof
  apply StatMech.Walls.bc37_armAdjacent_symm ω n h

/--
[bc37_armAdjacent_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armAdjacent_irrefl_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d} :
-- imply
  ¬ bc37_ArmAdjacent ω n x x := by
-- proof
  apply StatMech.Walls.bc37_armAdjacent_irrefl ω n x

/--
[bc37_armAdjGraph_le_trifGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armAdjGraph_le_trifGraph_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc37_armAdjGraph ω n ≤ stt_trifGraph ω n := by
-- proof
  apply StatMech.Walls.bc37_armAdjGraph_le_trifGraph ω n

/--
[bc37_sameCluster_of_armAdjReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_sameCluster_of_armAdjReachable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a b : {x : Site d // x ∈ tfc_trifFinset ω n}}
-- given
  (h : (bc37_armAdjGraph ω n).Reachable a b) :
-- imply
  Connected d ω a.1 b.1 := by
-- proof
  apply StatMech.Walls.bc37_sameCluster_of_armAdjReachable ω n h

/--
[bc37_isForest_iff_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_isForest_iff_isAcyclic_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  (bc37_armAdjGraph ω n).IsAcyclic ↔ ∀ ⦃a b⦄ (p q : (bc37_armAdjGraph ω n).Path a b), p = q := by
-- proof
  apply StatMech.Walls.bc37_isForest_iff_isAcyclic ω n

/--
[bc37_downArmSelector_of_armForestRooting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_downArmSelector_of_armForestRooting_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc37_ArmForestRooting ω n) :
-- imply
  bc37_DownArmSelector ω n := by
-- proof
  apply StatMech.Walls.bc37_downArmSelector_of_armForestRooting ω n h

/--
[bc37_selfDownArm_of_armForestRooting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_selfDownArm_of_armForestRooting_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc37_ArmForestRooting ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc37_selfDownArm_of_armForestRooting ω n h

/--
[bc37_armForestRooting_of_downArmSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armForestRooting_of_downArmSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc37_DownArmSelector ω n) :
-- imply
  bc37_ArmForestRooting ω n := by
-- proof
  apply StatMech.Walls.bc37_armForestRooting_of_downArmSelector ω n h

/--
[bc37_armForestRooting_iff_downArmSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armForestRooting_iff_downArmSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc37_ArmForestRooting ω n ↔ bc37_DownArmSelector ω n := by
-- proof
  apply StatMech.Walls.bc37_armForestRooting_iff_downArmSelector ω n

/--
[bc37_downArmSelector_of_singleCutSep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_downArmSelector_of_singleCutSep_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fcc_RootedSingleCutSeparation ω n) :
-- imply
  bc37_DownArmSelector ω n := by
-- proof
  apply StatMech.Walls.bc37_downArmSelector_of_singleCutSep ω n h

/--
[bc37_armForestRooting_of_singleCutSep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armForestRooting_of_singleCutSep_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fcc_RootedSingleCutSeparation ω n) :
-- imply
  bc37_ArmForestRooting ω n := by
-- proof
  apply StatMech.Walls.bc37_armForestRooting_of_singleCutSep ω n h

/--
[bc37_downArmSelector_of_parentFunneling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_downArmSelector_of_parentFunneling_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc37_ParentFunneling ω n) :
-- imply
  bc37_DownArmSelector ω n := by
-- proof
  apply StatMech.Walls.bc37_downArmSelector_of_parentFunneling ω n h

/--
[bc37_selfDownArm_of_parentFunneling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_selfDownArm_of_parentFunneling_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc37_ParentFunneling ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc37_selfDownArm_of_parentFunneling ω n h

/--
[bc37_armForestRooting_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armForestRooting_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc37_ArmForestRooting ω n := by
-- proof
  apply StatMech.Walls.bc37_armForestRooting_of_noTrif ω n hno

/--
[bc37_armForestRooting_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armForestRooting_of_twoTrif_eq
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
  (hdiv : ¬ Connected d (removeSite y₀ ω) (b y₀) (b x₀)) :
-- imply
  bc37_ArmForestRooting ω n := by
-- proof
  apply StatMech.Walls.bc37_armForestRooting_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hdiv

/--
[bc37_armForestRooting_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armForestRooting_of_threeChain_eq
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
  (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
-- imply
  bc37_ArmForestRooting ω n := by
-- proof
  apply StatMech.Walls.bc37_armForestRooting_of_threeChain ω n b hx0m hx0g hmg hthree hbx0 hbm hbg hsxm hsxg hsmg

/--
[bc37_armForestRooting_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armForestRooting_of_claw_eq
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
  bc37_ArmForestRooting ω n := by
-- proof
  apply StatMech.Walls.bc37_armForestRooting_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[bc37_armForestRooting_of_fourTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_armForestRooting_of_fourTree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g h : Site d}
  {b : Site d → Site d}
-- given
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hx0h : x₀ ≠ h)
  (hmg : m ≠ g)
  (hmh : m ≠ h)
  (hgh : g ≠ h)
  (hfour : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g ∨ x = h)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
  (hbh : b h ∈ box d n ∧ Connected d ω h (b h) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b h)).Infinite)
  (hm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hg_x0 : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hg_m : ¬ Connected d (removeSite g ω) (b g) (b m))
  (hh_x0 : ¬ Connected d (removeSite h ω) (b h) (b x₀))
  (hh_m : ¬ Connected d (removeSite h ω) (b h) (b m))
  (hh_g : ¬ Connected d (removeSite h ω) (b h) (b g)) :
-- imply
  bc37_ArmForestRooting ω n := by
-- proof
  apply StatMech.Walls.bc37_armForestRooting_of_fourTree ω n b hx0m hx0g hx0h hmg hmh hgh hfour hbx0 hbm hbg hbh hm hg_x0 hg_m hh_x0 hh_m hh_g

/--
[bc37_Tcount_le_boundary_of_armForestRooting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_Tcount_le_boundary_of_armForestRooting_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bc37_ArmForestRooting ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc37_Tcount_le_boundary_of_armForestRooting ω n hn h

/--
[bc37_burton_keane_bernoulli_of_armForestRooting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_burton_keane_bernoulli_of_armForestRooting_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc37_ArmForestRooting ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc37_burton_keane_bernoulli_of_armForestRooting hd p hp1 hp0 hres htrif

/--
[bc37_parentFunneling_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_parentFunneling_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc37_parentFunneling_of_noTrif ω n hno

/--
[bc37_parentFunneling_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_parentFunneling_of_twoTrif_eq
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
  (hlocal : ¬ Connected d (removeSite y₀ ω) (b y₀) (b x₀))
  (hself : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc37_parentFunneling_of_twoTrif ω n b hx0y0 htwo hbx0 hby0 hlocal hself

/--
[bc37_parentFunneling_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_parentFunneling_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b (y i))).Infinite)
  (hloc : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
  (hself : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) x₀)
  (hfun : ∀ i j : Fin 3, (j : ℕ) < i → Connected d (removeSite (y i) ω) (b (y j)) x₀) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc37_parentFunneling_of_claw ω n x₀ y b hx0box htri0 hydata hyinj hsingle hbx0 hby hloc hself hfun

/--
[bc37_claw_funnelShadow_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_claw_funnelShadow_consistent_eq
  {d : ℕ}
  {x0node bx0 : ℕ}
  {byv : Fin 3 → ℕ}
  {i : Fin 3}
-- given
  (hnode : x0node ≠ byv i)
  (hdistinct : ∀ j, byv j ≠ bx0)
  (hbyinj : Function.Injective byv) :
-- imply
  ∃ up : ℕ → Prop, (¬ up (byv i) ∧ up bx0) ∧ (¬ up (byv i) ∧ up x0node) ∧ (∀ j, j ≠ i → up x0node ∧ up (byv j)) := by
-- proof
  apply StatMech.Walls.bc37_claw_funnelShadow_consistent x0node bx0 byv i hnode hdistinct hbyinj

/--
[bc37_parentFunneling_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_parentFunneling_of_threeChain_eq
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
  (hlm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsm : ¬ Connected d (removeSite m ω) (b m) x₀)
  (hlg : ¬ Connected d (removeSite g ω) (b g) (b m))
  (hsg : ¬ Connected d (removeSite g ω) (b g) m)
  (hfg : Connected d (removeSite g ω) (b x₀) m) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc37_parentFunneling_of_threeChain ω n b hx0m hx0g hmg hthree hbx0 hbm hbg hlm hsm hlg hsg hfg

/--
[bc37_Tcount_le_boundary_of_parentFunneling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_Tcount_le_boundary_of_parentFunneling_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bc37_ParentFunneling ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc37_Tcount_le_boundary_of_parentFunneling ω n hn h

/--
[bc37_burton_keane_bernoulli_of_parentFunneling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean)
-/
@[path]
private lemma bc37_burton_keane_bernoulli_of_parentFunneling_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc37_ParentFunneling ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc37_burton_keane_bernoulli_of_parentFunneling hd p hp1 hp0 hres htrif


-- created on 2026-10-23
