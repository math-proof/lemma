import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc41rootside
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc41_not_connected_removeSite_cutSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_not_connected_removeSite_cutSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hxy : x ≠ y) :
-- imply
  ¬ Connected d (removeSite y ω) x y := by
-- proof
  apply StatMech.Walls.bc41_not_connected_removeSite_cutSite ω hxy

/--
[bc41_rootSideComparable_allPar_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_rootSideComparable_allPar_false_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (hy0box : y₀ ∈ box d n)
  (htriy0 : IsTrifurcation d ω y₀)
  (hne : x₀ ≠ y₀)
  (hconn : Connected d ω x₀ y₀) :
-- imply
  ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc40_RootSideComparable ω n rank par := by
-- proof
  apply StatMech.Walls.bc41_rootSideComparable_allPar_false ω n hx0box htri0 hy0box htriy0 hne hconn

/--
[bc41_rootSideComparableArm_not_trapped_at_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_rootSideComparableArm_not_trapped_at_self_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {y₀ : Site d} :
-- imply
  bc37_ArmAdjacent ω n y₀ ((fun _ => y₀) y₀) → False := by
-- proof
  apply StatMech.Walls.bc41_rootSideComparableArm_not_trapped_at_self ω n rank

/--
[bc41_armRealisation_of_cutGeometryFixed'_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_armRealisation_of_cutGeometryFixed'_arm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootSideComparableArm ω n rank par) :
-- imply
  bc38_ArmRealisation ω n := by
-- proof
  apply StatMech.Walls.bc41_armRealisation_of_cutGeometryFixed'_arm ω n hgeo hroot_side

/--
[bc41_parentFunneling_of_cutGeometryFixed'_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_parentFunneling_of_cutGeometryFixed'_arm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootSideComparableArm ω n rank par) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc41_parentFunneling_of_cutGeometryFixed'_arm ω n hgeo hroot_side

/--
[bc41_selfDownArm_of_cutGeometryFixed'_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_selfDownArm_of_cutGeometryFixed'_arm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootSideComparableArm ω n rank par) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc41_selfDownArm_of_cutGeometryFixed'_arm ω n hgeo hroot_side

/--
[bc41_burton_keane_bernoulli_of_cutGeometryFixed'_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_burton_keane_bernoulli_of_cutGeometryFixed'_arm_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
  (hroot_side : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootSideComparableArm ω n rank par)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc41_burton_keane_bernoulli_of_cutGeometryFixed'_arm hd p hp1 hp0 hgeo hroot_side htrif

/--
[bc41_rootSideComparableArm_of_rootWardAvoidingWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_rootSideComparableArm_of_rootWardAvoidingWalk_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {par : Site d → Site d}
-- given
  (hwalk : bc41_RootWardAvoidingWalk ω n rank par) :
-- imply
  bc41_RootSideComparableArm ω n rank par := by
-- proof
  apply StatMech.Walls.bc41_rootSideComparableArm_of_rootWardAvoidingWalk ω n rank par hwalk

/--
[bc41_burton_keane_bernoulli_of_rootWardAvoidingWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_burton_keane_bernoulli_of_rootWardAvoidingWalk_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc40_ArmCutGeometryFixed' ω n)
  (hwalk : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d), bc41_RootWardAvoidingWalk ω n rank par)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc41_burton_keane_bernoulli_of_rootWardAvoidingWalk hd p hp1 hp0 hgeo hwalk htrif

/--
[bc41_rootWardAvoidingWalk_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_rootWardAvoidingWalk_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {par : Site d → Site d}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc41_RootWardAvoidingWalk ω n rank par := by
-- proof
  apply StatMech.Walls.bc41_rootWardAvoidingWalk_of_noTrif ω n rank par hno

/--
[bc41_rootSideComparableArm_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_rootSideComparableArm_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {par : Site d → Site d}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc41_RootSideComparableArm ω n rank par := by
-- proof
  apply StatMech.Walls.bc41_rootSideComparableArm_of_noTrif ω n rank par hno

/--
[bc41_rootWardAvoidingWalk_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_rootWardAvoidingWalk_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hx0y0 : x₀ ≠ y₀) :
-- imply
  bc41_RootWardAvoidingWalk ω n rank (fun _ => x₀) := by
-- proof
  apply StatMech.Walls.bc41_rootWardAvoidingWalk_of_twoTrif ω n rank htwo hx0y0

/--
[bc41_rootSideComparableArm_of_twoTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_rootSideComparableArm_of_twoTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ y₀ : Site d}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
  (hx0y0 : x₀ ≠ y₀) :
-- imply
  bc41_RootSideComparableArm ω n rank (fun _ => x₀) := by
-- proof
  apply StatMech.Walls.bc41_rootSideComparableArm_of_twoTrif ω n rank htwo hx0y0

/--
[bc41_cutGeometryFixed'_downArm_guard_vacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_cutGeometryFixed'_downArm_guard_vacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {t s : Site d}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (htbox : t ∈ box d n)
  (htri : IsTrifurcation d ω t)
  (hadj : bc37_ArmAdjacent ω n t s) :
-- imply
  ∃ b : Site d → Site d, ¬ Connected d (removeSite t ω) (b t) s := by
-- proof
  apply StatMech.Walls.bc41_cutGeometryFixed'_downArm_guard_vacuous ω n hgeo htbox htri hadj

/--
[bc41_cutGeometryFixed'_no_downArm_trap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc41rootside.lean)
-/
@[path]
private lemma bc41_cutGeometryFixed'_no_downArm_trap_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {t s : Site d}
-- given
  (hgeo : bc40_ArmCutGeometryFixed' ω n)
  (htbox : t ∈ box d n)
  (htri : IsTrifurcation d ω t)
  (hadj : bc37_ArmAdjacent ω n t s) :
-- imply
  ∃ b : Site d → Site d, (∀ x, x ≠ t → Connected d (removeSite t ω) x s → Connected d (removeSite t ω) (b x) s) ∧ ¬ Connected d (removeSite t ω) (b t) s := by
-- proof
  apply StatMech.Walls.bc41_cutGeometryFixed'_no_downArm_trap ω n hgeo htbox htri hadj


-- created on 2026-10-23
