import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc43rootparent
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc43_rootWardRootParent_of_rootWardAvoidingWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_rootWardRootParent_of_rootWardAvoidingWalk_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {par : Site d → Site d}
-- given
  (hold : bc41_RootWardAvoidingWalk ω n rank par) :
-- imply
  bc43_RootWardRootParent ω n rank par := by
-- proof
  apply StatMech.Walls.bc43_rootWardRootParent_of_rootWardAvoidingWalk ω n rank par hold

/--
[bc43_farWitness_rank_not_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_farWitness_rank_not_injective_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ z₀ : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hz0box : z₀ ∈ box d n)
  (htriz0 : IsTrifurcation d ω z₀)
  (hne : x₀ ≠ y₀)
  (hz0y0 : z₀ ≠ y₀)
  (hx0z0 : x₀ ≠ z₀)
  (hconnxz : Connected d ω x₀ z₀) :
-- imply
  ¬ (∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b → a ≠ b → Connected d ω a b → (fun w => toLex (if w = y₀ then (1 : ℕ) else 0, (0 : ℕ))) a ≠ (fun w => toLex (if w = y₀ then (1 : ℕ) else 0, (0 : ℕ))) b) := by
-- proof
  apply StatMech.Walls.bc43_farWitness_rank_not_injective ω n hx0box htri0 hz0box htriz0 hne hz0y0 hx0z0 hconnxz

/--
[bc43_rootWardRootParent_no_farParent_trap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_rootWardRootParent_no_farParent_trap_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ z₀ : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hz0box : z₀ ∈ box d n)
  (htriz0 : IsTrifurcation d ω z₀)
  (hne : x₀ ≠ y₀)
  (hz0y0 : z₀ ≠ y₀)
  (hx0z0 : x₀ ≠ z₀)
  (hconnxz : Connected d ω x₀ z₀)
  (hfar : ¬ Connected d (removeSite y₀ ω) x₀ z₀) :
-- imply
  bc43_RootWardRootParent ω n (fun w => toLex (if w = y₀ then (1 : ℕ) else 0, (0 : ℕ))) (fun _ => z₀) := by
-- proof
  apply StatMech.Walls.bc43_rootWardRootParent_no_farParent_trap ω n hx0box htri0 hz0box htriz0 hne hz0y0 hx0z0 hconnxz hfar

/--
[bc43_rootWardRootParent_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_rootWardRootParent_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {par : Site d → Site d}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc43_RootWardRootParent ω n rank par := by
-- proof
  apply StatMech.Walls.bc43_rootWardRootParent_of_noTrif ω n rank par hno

/--
[bc43_rootWardRootParent_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_rootWardRootParent_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
-- given
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hx0y0 : x₀ ≠ y₀) :
-- imply
  ∀ (rank : Site d → ℕ ×ₗ ℕ), bc43_RootWardRootParent ω n rank (fun _ => x₀) := by
-- proof
  apply StatMech.Walls.bc43_rootWardRootParent_of_twoTrif ω n htwo hx0y0

/--
[bc43_rootWardRootParent_of_twoTrif_allPar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_rootWardRootParent_of_twoTrif_allPar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
-- given
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hx0y0 : x₀ ≠ y₀) :
-- imply
  ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc43_RootWardRootParent ω n rank par := by
-- proof
  apply StatMech.Walls.bc43_rootWardRootParent_of_twoTrif_allPar ω n htwo hx0y0

/--
[bc43_exists_rootedArmForest_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_exists_rootedArmForest_mem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∃ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧ (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x < rank y → par y ∈ tfc_trifFinset ω n ∧ bc37_ArmAdjacent ω n y (par y) ∧ rank (par y) < rank y) := by
-- proof
  apply StatMech.Walls.bc43_exists_rootedArmForest_mem ω n

/--
[bc43_parentFunneling_of_cutGeometryFixed'_rootParent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_parentFunneling_of_cutGeometryFixed'_rootParent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hwalk : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc43_RootWardRootParent ω n rank par) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc43_parentFunneling_of_cutGeometryFixed'_rootParent ω n hgeo hwalk

/--
[bc43_selfDownArm_of_cutGeometryFixed'_rootParent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_selfDownArm_of_cutGeometryFixed'_rootParent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hwalk : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc43_RootWardRootParent ω n rank par) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc43_selfDownArm_of_cutGeometryFixed'_rootParent ω n hgeo hwalk

/--
[bc43_burton_keane_bernoulli_of_rootWardRootParent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc43rootparent.lean)
-/
@[path]
private lemma bc43_burton_keane_bernoulli_of_rootWardRootParent_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
  (hwalk : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc43_RootWardRootParent ω n rank par)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc43_burton_keane_bernoulli_of_rootWardRootParent hd p hp1 hp0 hgeo hwalk htrif


-- created on 2026-10-23
