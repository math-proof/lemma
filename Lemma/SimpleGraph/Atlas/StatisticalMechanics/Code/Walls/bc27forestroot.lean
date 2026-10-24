import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc27forestroot
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc27_privateFar_forces_arm_meets_child](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_privateFar_forces_arm_meets_child_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₀ bx₀ : Site d}
  {y : Fin 3 → Site d}
  {lx : Site d → Fin 3}
-- given
  (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v → (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
  (hydown : ∀ i, lx (y i) = i)
  (hydata : ∀ i, x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hbxconn : Connected d ω x₀ bx₀)
  (hbxne : x₀ ≠ bx₀) :
-- imply
  bkfl_inArm ω x₀ bx₀ (y (lx bx₀)) := by
-- proof
  apply StatMech.Walls.bc27_privateFar_forces_arm_meets_child ω hlxf hydown hydata hbxconn hbxne

/--
[bc27_not_privateFarOrder_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_not_privateFarOrder_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : stac_ClawConfig ω n) :
-- imply
  ¬ bc26_PrivateFarOrder ω n := by
-- proof
  apply StatMech.Walls.bc27_not_privateFarOrder_of_claw ω n hclaw

/--
[bc27_privateFarOrder_not_universal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_privateFarOrder_not_universal_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : stac_ClawConfig ω n) :
-- imply
  ¬ bc26_PrivateFarOrder ω n := by
-- proof
  apply StatMech.Walls.bc27_privateFarOrder_not_universal ω n hclaw

/--
[bc27_not_coherentSelector_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_not_coherentSelector_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hclaw : stac_ClawConfig ω n) :
-- imply
  ¬ bkfl_CoherentArmSelector ω n := by
-- proof
  apply StatMech.Walls.bc27_not_coherentSelector_of_claw ω n hclaw

/--
[bc27_globalForestArms_of_rootedTreeArmSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_globalForestArms_of_rootedTreeArmSelection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bas_RootedTreeArmSelection ω n) :
-- imply
  aed_GlobalForestArms ω n := by
-- proof
  apply StatMech.Walls.bc27_globalForestArms_of_rootedTreeArmSelection ω n h

/--
[bc27_count_of_rootedTreeArmSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_count_of_rootedTreeArmSelection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bas_RootedTreeArmSelection ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc27_count_of_rootedTreeArmSelection ω n hn h

/--
[bc27_burton_keane_bernoulli_of_rootedTreeArmSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_burton_keane_bernoulli_of_rootedTreeArmSelection_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bas_RootedTreeArmSelection ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc27_burton_keane_bernoulli_of_rootedTreeArmSelection hd p hp1 hp0 hres htrif

/--
[bc27_rootedTreeArmSelection_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_rootedTreeArmSelection_of_claw_eq
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
  bas_RootedTreeArmSelection ω n := by
-- proof
  apply StatMech.Walls.bc27_rootedTreeArmSelection_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[bc27_privateFarOrder_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_privateFarOrder_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc26_PrivateFarOrder ω n := by
-- proof
  apply StatMech.Walls.bc27_privateFarOrder_of_noTrif ω n hno

/--
[bc27_privateFarOrder_of_uniqueTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_privateFarOrder_of_uniqueTrif_eq
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
  apply StatMech.Walls.bc27_privateFarOrder_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq

/--
[bc27_privateFarOrder_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc27forestroot.lean)
-/
@[path]
private lemma bc27_privateFarOrder_of_twoTrif_eq
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
  apply StatMech.Walls.bc27_privateFarOrder_of_twoTrif ω n b hx0y0 htwo hdata_x hdata_y hpf_xy hpf_yx


-- created on 2026-10-23
