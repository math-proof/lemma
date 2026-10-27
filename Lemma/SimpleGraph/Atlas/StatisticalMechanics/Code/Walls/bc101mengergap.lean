import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc101_gnTrif_three_incident_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc101mengergap.lean)
-/
@[path]
private lemma bc101_gnTrif_three_incident_arms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧ (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧ (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧ (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc101_gnTrif_three_incident_arms ω L y h

/--
[bc101_arm_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc101mengergap.lean)
-/
@[path]
private lemma bc101_arm_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a : Site d}
-- given
  (hR : 1 ≤ R)
  (habox : a ∈ box d R)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z := by
-- proof
  apply StatMech.Walls.bc101_arm_reaches_boundary ω L R hR y a habox hinf

/--
[bc101_mngg_available_but_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc101mengergap.lean)
-/
@[path]
private lemma bc101_mngg_available_but_free_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc101_mngg_available_but_free ω L y h

/--
[bc101_residue_is_boundary_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc101mengergap.lean)
-/
@[path]
private lemma bc101_residue_is_boundary_injection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc61_CoarseForestLeafCount ω L R := by
-- proof
  apply StatMech.Walls.bc101_residue_is_boundary_injection ω L R hz₀ hz₁ hzne hinj

/--
[bc101_coarseTcount_of_boundaryInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc101mengergap.lean)
-/
@[path]
private lemma bc101_coarseTcount_of_boundaryInjection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc101_coarseTcount_of_boundaryInjection ω L R hz₀ hz₁ hzne hinj

/--
[bc101_named_residue_wrong_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc101mengergap.lean)
-/
@[path]
private lemma bc101_named_residue_wrong_scale_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bc56_BoxClusterReachesNbr 2 3 := by
-- proof
  apply StatMech.Walls.bc101_named_residue_wrong_scale hL

/--
[bc101_three_arms_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc101mengergap.lean)
-/
@[path]
private lemma bc101_three_arms_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ a₁ a₂ a₃ : Site 2, (bc67_GnIncident bc60_upperLines L 0 a₁ ∧ bc67_GnIncident bc60_upperLines L 0 a₂ ∧ bc67_GnIncident bc60_upperLines L 0 a₃) ∧ (¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc101_three_arms_upperLines hL

/--
[bc101_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc101mengergap.lean)
-/
@[path]
private lemma bc101_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)) ∧ (∀ {L : ℕ}, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bc56_BoxClusterReachesNbr 2 3) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → bc64_CoarseBoundaryInjection ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc101_status


-- created on 2026-10-23
