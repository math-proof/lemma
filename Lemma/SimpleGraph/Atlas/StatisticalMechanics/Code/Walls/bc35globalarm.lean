import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc35_downArmSplit_of_privateFar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc35globalarm.lean)
-/
@[path]
private lemma bc35_downArmSplit_of_privateFar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {b : Site d → Site d}
  {x y : Site d}
-- given
  (h : bkfl_PrivateFar ω b y x) :
-- imply
  ¬ Connected d (removeSite y ω) (b y) (b x) := by
-- proof
  apply StatMech.Walls.bc35_downArmSplit_of_privateFar ω b h

/--
[bc35_TavoidingRayData_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc35globalarm.lean)
-/
@[path]
private lemma bc35_TavoidingRayData_of_rootedArmDivergence_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : rfp_RootedArmDivergence ω n) :
-- imply
  ∃ rank : Site d → ℕ ×ₗ ℕ, bc33_TavoidingRayData ω n rank := by
-- proof
  apply StatMech.Walls.bc35_TavoidingRayData_of_rootedArmDivergence ω n h

/--
[bc35_burton_keane_bernoulli_of_rootedArmDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc35globalarm.lean)
-/
@[path]
private lemma bc35_burton_keane_bernoulli_of_rootedArmDivergence_eq
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
  apply StatMech.Walls.bc35_burton_keane_bernoulli_of_rootedArmDivergence hd p hp1 hp0 hres htrif

/--
[bc35_TavoidingRayData_of_coherentSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc35globalarm.lean)
-/
@[path]
private lemma bc35_TavoidingRayData_of_coherentSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc26_PrivateFarOrder ω n) :
-- imply
  bc33_TavoidingRayData ω n rank := by
-- proof
  apply StatMech.Walls.bc35_TavoidingRayData_of_coherentSelector ω n rank h

/--
[bc35_globalCutArm_of_singleCutTfree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc35globalarm.lean)
-/
@[path]
private lemma bc35_globalCutArm_of_singleCutTfree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x bx : Site d}
-- given
  (hbbox : bx ∈ box d n)
  (hbconn : Connected d ω x bx)
  (hinf : (cluster d (removeSite x ω) bx).Infinite)
  (hTfree : ∀ z, Connected d (removeSite x ω) bx z → z ∉ tfc_trifFinset ω n) :
-- imply
  bx ∈ box d n ∧ Connected d ω x bx ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) bx).Infinite := by
-- proof
  apply StatMech.Walls.bc35_globalCutArm_of_singleCutTfree ω n hbbox hbconn hinf hTfree

/--
[bc35_globalCutArm_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc35globalarm.lean)
-/
@[path]
private lemma bc35_globalCutArm_of_threeChain_eq
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
  (harm : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
-- imply
  bc33_TavoidingRayData ω n (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc35_globalCutArm_of_threeChain ω n b hx0box hmbox hgbox hx0m hx0g hmg hthree harm hsxm hsxg hsmg

/--
[bc35_globalCutArm_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc35globalarm.lean)
-/
@[path]
private lemma bc35_globalCutArm_of_claw_eq
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
  (harm : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
  (hssib : ∀ i j : Fin 3, (j : ℕ) < i → ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
-- imply
  bc33_TavoidingRayData ω n (fun z => if z = x₀ then toLex (0, 0) else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc35_globalCutArm_of_claw ω n x₀ y b hx0box hydata hyinj hsingle harm hsx0 hssib

/--
[bc35_TavoidingRayData_of_clawArmGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc35globalarm.lean)
-/
@[path]
private lemma bc35_TavoidingRayData_of_clawArmGeometry_eq
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
  ∃ rank : Site d → ℕ ×ₗ ℕ, bc33_TavoidingRayData ω n rank := by
-- proof
  apply StatMech.Walls.bc35_TavoidingRayData_of_clawArmGeometry ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar hsingle b hbdata hcy hcx hcentral


-- created on 2026-10-23
