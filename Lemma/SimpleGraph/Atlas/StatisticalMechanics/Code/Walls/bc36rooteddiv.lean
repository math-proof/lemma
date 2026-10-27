import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc36_rootedArmDivergence_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_rootedArmDivergence_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc36_rootedArmDivergence_of_noTrif ω n hno

/--
[bc36_rootedArmDivergence_of_selfDownArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_rootedArmDivergence_of_selfDownArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc36_SelfDownArm ω n) :
-- imply
  rfp_RootedArmDivergence ω n := by
-- proof
  apply StatMech.Walls.bc36_rootedArmDivergence_of_selfDownArm ω n h

/--
[bc36_selfDownArm_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_selfDownArm_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc36_selfDownArm_of_noTrif ω n hno

/--
[bc36_selfDownArm_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_selfDownArm_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {b : Site d → Site d}
  {dn : Site d → Site d}
-- given
  (hx0y0 : x₀ ≠ y₀)
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
  (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
  (hself : Connected d (removeSite y₀ ω) (dn y₀) (b y₀))
  (havoid : ¬ Connected d (removeSite y₀ ω) (dn y₀) (b x₀)) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc36_selfDownArm_of_twoTrif ω n b dn hx0y0 htwo hbx0 hby0 hself havoid

/--
[bc36_selfDownArm_of_fourTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_selfDownArm_of_fourTree_eq
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
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc36_selfDownArm_of_fourTree ω n b hx0m hx0g hx0h hmg hmh hgh hfour hbx0 hbm hbg hbh hm hg_x0 hg_m hh_x0 hh_m hh_g

/--
[bc36_selfDownArm_of_singleCutSep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_selfDownArm_of_singleCutSep_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : fcc_RootedSingleCutSeparation ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc36_selfDownArm_of_singleCutSep ω n h

/--
[bc36_selfDownArm_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_selfDownArm_of_claw_eq
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
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc36_selfDownArm_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar hsingle b hbdata hcy hcx hcentral

/--
[bc36_Tcount_le_boundary_of_selfDownArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_Tcount_le_boundary_of_selfDownArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (h : bc36_SelfDownArm ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc36_Tcount_le_boundary_of_selfDownArm ω n hn h

/--
[bc36_burton_keane_bernoulli_of_selfDownArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc36rooteddiv.lean)
-/
@[path]
private lemma bc36_burton_keane_bernoulli_of_selfDownArm_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc36_SelfDownArm ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0 hres htrif


-- created on 2026-10-23
