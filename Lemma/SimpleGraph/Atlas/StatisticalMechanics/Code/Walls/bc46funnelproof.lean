import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc46funnelproof
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc46_openEdge_removeSite_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_openEdge_removeSite_of_ne_eq
  {d : ℕ}
  {t : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (htu : t ≠ u)
  (htv : t ≠ v)
  (h : IsOpenEdge d ω u v) :
-- imply
  IsOpenEdge d (removeSite t ω) u v := by
-- proof
  apply StatMech.Walls.bc46_openEdge_removeSite_of_ne t ω htu htv h

/--
[bc46_armLink_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_armLink_survives_eq
  {d : ℕ}
  {t : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x bx : Site d}
-- given
  (htx : t ≠ x)
  (htbx : t ≠ bx)
  (hedge : IsOpenEdge d ω x bx) :
-- imply
  Connected d (removeSite t ω) x bx := by
-- proof
  apply StatMech.Walls.bc46_armLink_survives t ω htx htbx hedge

/--
[bc46_armCutGeometryFixed'_of_armFunnelGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_armCutGeometryFixed'_of_armFunnelGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc46_ArmFunnelGeometry ω n) :
-- imply
  bc40_ArmCutGeometryFixed' ω n := by
-- proof
  apply StatMech.Walls.bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n hgeo

/--
[bc46_armFunnelGeometry_of_neighborArmFunnel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_armFunnelGeometry_of_neighborArmFunnel_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc46_NeighborArmFunnel ω n) :
-- imply
  bc46_ArmFunnelGeometry ω n := by
-- proof
  apply StatMech.Walls.bc46_armFunnelGeometry_of_neighborArmFunnel ω n hgeo

/--
[bc46_parentFunneling_of_armFunnelGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_parentFunneling_of_armFunnelGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc46_ArmFunnelGeometry ω n) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc46_parentFunneling_of_armFunnelGeometry ω n hgeo

/--
[bc46_selfDownArm_of_armFunnelGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_selfDownArm_of_armFunnelGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc46_ArmFunnelGeometry ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc46_selfDownArm_of_armFunnelGeometry ω n hgeo

/--
[bc46_burton_keane_bernoulli_of_armFunnelGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_burton_keane_bernoulli_of_armFunnelGeometry_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc46_ArmFunnelGeometry ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc46_burton_keane_bernoulli_of_armFunnelGeometry hd p hp1 hp0 hgeo htrif

/--
[bc46_burton_keane_bernoulli_of_neighborArmFunnel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_burton_keane_bernoulli_of_neighborArmFunnel_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc46_NeighborArmFunnel ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc46_burton_keane_bernoulli_of_neighborArmFunnel hd p hp1 hp0 hgeo htrif

/--
[bc46_parentFunneling_of_correctedParentGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_parentFunneling_of_correctedParentGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc46_CorrectedParentGeometry ω n) :
-- imply
  bc37_ParentFunneling ω n := by
-- proof
  apply StatMech.Walls.bc46_parentFunneling_of_correctedParentGeometry ω n hgeo

/--
[bc46_selfDownArm_of_correctedParentGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_selfDownArm_of_correctedParentGeometry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hgeo : bc46_CorrectedParentGeometry ω n) :
-- imply
  bc36_SelfDownArm ω n := by
-- proof
  apply StatMech.Walls.bc46_selfDownArm_of_correctedParentGeometry ω n hgeo

/--
[bc46_burton_keane_bernoulli_of_correctedParentGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_burton_keane_bernoulli_of_correctedParentGeometry_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc46_CorrectedParentGeometry ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc46_burton_keane_bernoulli_of_correctedParentGeometry hd p hp1 hp0 hgeo htrif

/--
[bc46_correctedParentGeometry_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_correctedParentGeometry_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc46_CorrectedParentGeometry ω n := by
-- proof
  apply StatMech.Walls.bc46_correctedParentGeometry_of_noTrif ω n hno

/--
[bc46_clawShadow_hubCut_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_clawShadow_hubCut_fails_eq
  {d : ℕ} :
-- imply
  ¬ ((bc46_clawLab 0 (bc46_clawB 0) ≠ bc46_clawLab 0 (bc46_clawB 1)) ∧ (bc46_clawLab 0 (bc46_clawB 0) ≠ bc46_clawLab 0 1)) := by
-- proof
  apply StatMech.Walls.bc46_clawShadow_hubCut_fails

/--
[bc46_clawShadow_funnelAtParent_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_clawShadow_funnelAtParent_fails_eq
  {d : ℕ} :
-- imply
  (0 : Fin 10) ≠ 1 ∧ bc46_clawLab 1 0 = bc46_clawLab 1 0 ∧ bc46_clawLab 1 (bc46_clawB 0) ≠ bc46_clawLab 1 0 := by
-- proof
  apply StatMech.Walls.bc46_clawShadow_funnelAtParent_fails

/--
[bc46_clawShadow_pipeline_clauses_ok](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_clawShadow_pipeline_clauses_ok_eq
  {d : ℕ} :
-- imply
  (bc46_clawLab 1 (bc46_clawB 1) ≠ bc46_clawLab 1 (bc46_clawB 0)) ∧ (bc46_clawLab 1 (bc46_clawB 1) ≠ bc46_clawLab 1 0) ∧ (∀ x : Fin 10, x ≠ 1 → x ≠ 0 → bc46_clawLab 1 x = bc46_clawLab 1 0 → bc46_clawLab 1 (bc46_clawB x) = bc46_clawLab 1 0) := by
-- proof
  apply StatMech.Walls.bc46_clawShadow_pipeline_clauses_ok

/--
[bc46_clawShadow_guard_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_clawShadow_guard_nontrivial_eq
  {d : ℕ} :
-- imply
  (bc46_clawLab 1 2 = bc46_clawLab 1 0 ∧ bc46_clawLab 1 3 = bc46_clawLab 1 0) ∧ (bc46_clawLab 1 4 ≠ bc46_clawLab 1 0 ∧ bc46_clawLab 1 5 ≠ bc46_clawLab 1 0) := by
-- proof
  apply StatMech.Walls.bc46_clawShadow_guard_nontrivial

/--
[bc46_clawShadow_correctedParentGeometry_ok](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_clawShadow_correctedParentGeometry_ok_eq
  {d : ℕ} :
-- imply
  (∀ y : Fin 10, (y = 1 ∨ y = 2 ∨ y = 3) → (bc46_clawLab y (bc46_clawB y) ≠ bc46_clawLab y (bc46_clawB 0)) ∧ (bc46_clawLab y (bc46_clawB y) ≠ bc46_clawLab y 0)) ∧ (∀ y : Fin 10, (y = 1 ∨ y = 2 ∨ y = 3) → ∀ x : Fin 10, x ≠ y → x ≠ 0 → bc46_clawLab y x = bc46_clawLab y 0 → bc46_clawLab y (bc46_clawB x) = bc46_clawLab y 0) := by
-- proof
  apply StatMech.Walls.bc46_clawShadow_correctedParentGeometry_ok

/--
[bc46_chainShadow_all_clauses_hold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_chainShadow_all_clauses_hold_eq
  {d : ℕ} :
-- imply
  ∀ t s : Fin 8, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) ∨ (t = 2 ∧ s = 3) ∨ (t = 3 ∧ s = 2) → (bc46_chainLab t (bc46_chainB t) ≠ bc46_chainLab t (bc46_chainB s)) ∧ (bc46_chainLab t (bc46_chainB t) ≠ bc46_chainLab t s) ∧ (∀ x : Fin 8, x ≠ t → bc46_chainLab t x = bc46_chainLab t s → bc46_chainLab t (bc46_chainB x) = bc46_chainLab t s) := by
-- proof
  apply StatMech.Walls.bc46_chainShadow_all_clauses_hold

/--
[bc46_chainShadow_guard_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean)
-/
@[path]
private lemma bc46_chainShadow_guard_nontrivial_eq
  {d : ℕ} :
-- imply
  (bc46_chainLab 2 0 = bc46_chainLab 2 1 ∧ bc46_chainLab 2 5 = bc46_chainLab 2 1) ∧ (bc46_chainLab 2 3 ≠ bc46_chainLab 2 1 ∧ bc46_chainLab 2 7 ≠ bc46_chainLab 2 1) := by
-- proof
  apply StatMech.Walls.bc46_chainShadow_guard_nontrivial


-- created on 2026-10-23
