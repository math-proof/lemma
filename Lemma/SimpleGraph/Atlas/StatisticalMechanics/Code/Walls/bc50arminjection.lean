import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc50arminjection.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc50_injection_of_countBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_injection_of_countBound_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hcount : bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n) :
-- imply
  bc48_ClassicalBoundaryArmInjection ω n := by
-- proof
  apply StatMech.Walls.bc50_injection_of_countBound ω n hcount

/--
[bc50_countBound_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_countBound_of_injection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc48_ClassicalBoundaryArmInjection ω n) :
-- imply
  bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc50_countBound_of_injection ω n h

/--
[bc50_injection_iff_countBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_injection_iff_countBound_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc48_ClassicalBoundaryArmInjection ω n ↔ bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc50_injection_iff_countBound ω n

/--
[bc50_arms_reach_distinct_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_arms_reach_distinct_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hxbox : x ∈ box d n)
  (hcl : bc47_IsClassicalTrifurcation ω x) :
-- imply
  ∃ a₁ a₂ a₃ z₁ z₂ z₃ : Site d, (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) ∧ (z₁ ∈ vertexBoundary d (n + 1) ∧ z₂ ∈ vertexBoundary d (n + 1) ∧ z₃ ∈ vertexBoundary d (n + 1)) ∧ ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧ (Connected d (removeSite x ω) a₁ z₁ ∧ Connected d (removeSite x ω) a₂ z₂ ∧ Connected d (removeSite x ω) a₃ z₃) := by
-- proof
  apply StatMech.Walls.bc50_arms_reach_distinct_boundary ω n x hxbox hcl

/--
[bc50_classical_countBound_of_armForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_classical_countBound_of_armForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : sfa_ArmForestReaching ω n) :
-- imply
  bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc50_classical_countBound_of_armForest ω n h

/--
[bc50_ClassicalBoundaryArmInjection_of_armForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_ClassicalBoundaryArmInjection_of_armForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : sfa_ArmForestReaching ω n) :
-- imply
  bc48_ClassicalBoundaryArmInjection ω n := by
-- proof
  apply StatMech.Walls.bc50_ClassicalBoundaryArmInjection_of_armForest ω n h

/--
[bc50_ClassicalBoundaryArmInjection_of_armForest_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_ClassicalBoundaryArmInjection_of_armForest_all_eq
  {d : ℕ}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), sfa_ArmForestReaching ω n) :
-- imply
  ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n := by
-- proof
  apply StatMech.Walls.bc50_ClassicalBoundaryArmInjection_of_armForest_all h

/--
[bc50_burton_keane_bernoulli_of_armForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_burton_keane_bernoulli_of_armForest_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), sfa_ArmForestReaching ω n)
  (hroute : ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc50_burton_keane_bernoulli_of_armForest hd p hp1 hp0 harm hroute

/--
[bc50_burton_keane_bernoulli_of_armForest_routingCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_burton_keane_bernoulli_of_armForest_routingCover_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (harm : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), sfa_ArmForestReaching ω n)
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc50_burton_keane_bernoulli_of_armForest_routingCover hd p hp1 hp0 harm hrt

/--
[bc50_injection_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_injection_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc48_ClassicalBoundaryArmInjection ω n := by
-- proof
  apply StatMech.Walls.bc50_injection_of_noTrif ω n hno

/--
[bc50_countBound_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_countBound_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc50_countBound_of_noTrif ω n hno

/--
[bc50_armEndpoint_map_not_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_armEndpoint_map_not_injective_eq
  {d : ℕ} :
-- imply
  bc50_shadowArmEnd 0 0 = bc50_shadowArmEnd 1 0 ∧ (0 : Fin 2) ≠ 1 := by
-- proof
  apply StatMech.Walls.bc50_armEndpoint_map_not_injective

/--
[bc50_abstract_injection_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_abstract_injection_exists_eq
  {d : ℕ} :
-- imply
  ∃ ψ : Fin 2 → Fin 5, Function.Injective ψ ∧ (∀ h, ψ h = 2 ∨ ψ h = 3 ∨ ψ h = 4) := by
-- proof
  apply StatMech.Walls.bc50_abstract_injection_exists

/--
[bc50_injection_notOverStrong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_injection_notOverStrong_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  (bc48_ClassicalBoundaryArmInjection ω n ↔ bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n) ∧ (¬ bc48_ClassicalBoundaryArmInjection ω n ↔ boxSV_boundaryCard d n < bc48_Tcount_classical d ω n) := by
-- proof
  apply StatMech.Walls.bc50_injection_notOverStrong ω n

/--
[bc50_clawShadow_distinct_boundary_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean)
-/
@[path]
private lemma bc50_clawShadow_distinct_boundary_fires_eq
  {d : ℕ} :
-- imply
  ∀ c : Fin 10, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) → ∃ n₁ n₂ n₃ : Fin 10, (bc46_clawLab c n₁ ≠ bc46_clawLab c n₂ ∧ bc46_clawLab c n₁ ≠ bc46_clawLab c n₃ ∧ bc46_clawLab c n₂ ≠ bc46_clawLab c n₃) ∧ (∃ z₁, bc46_clawLab c z₁ = bc46_clawLab c n₁ ∧ bc47_clawIsArm z₁ = true) ∧ (∃ z₂, bc46_clawLab c z₂ = bc46_clawLab c n₂ ∧ bc47_clawIsArm z₂ = true) ∧ (∃ z₃, bc46_clawLab c z₃ = bc46_clawLab c n₃ ∧ bc47_clawIsArm z₃ = true) := by
-- proof
  apply StatMech.Walls.bc50_clawShadow_distinct_boundary_fires


-- created on 2026-10-23
