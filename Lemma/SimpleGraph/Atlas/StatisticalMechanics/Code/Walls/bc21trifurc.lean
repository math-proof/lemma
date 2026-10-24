import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc21trifurc
open Set SimpleGraph MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc21_mengerCore_of_canonicalTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_mengerCore_of_canonicalTrifurcation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (htri : IsCanonicalTrifurcation d ω 0) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Walls.bc21_mengerCore_of_canonicalTrifurcation ω htri

/--
[bc21_mengerCore_of_originBranchSurvivalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_mengerCore_of_originBranchSurvivalCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc21_OriginBranchSurvivalCut d ω) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Walls.bc21_mengerCore_of_originBranchSurvivalCut ω h

/--
[bc21_originBranchSurvivalCut_of_canonicalTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_originBranchSurvivalCut_of_canonicalTrifurcation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (htri : IsCanonicalTrifurcation d ω 0) :
-- imply
  bc21_OriginBranchSurvivalCut d ω := by
-- proof
  apply StatMech.Walls.bc21_originBranchSurvivalCut_of_canonicalTrifurcation ω htri

/--
[bc21_arm_infinite_removeOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_arm_infinite_removeOrigin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (htri : IsCanonicalTrifurcation d ω 0) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃) ∧ (∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) a₁ y) ∧ (∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) a₂ y) ∧ (∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) a₃ y) := by
-- proof
  apply StatMech.Walls.bc21_arm_infinite_removeOrigin ω htri

/--
[bc21_mengerRoutingCover_of_boxTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_mengerRoutingCover_of_boxTrifurcation_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc12_BoxOriginTrifurcation d n) :
-- imply
  MengerRoutingCover d n := by
-- proof
  apply StatMech.Walls.bc21_mengerRoutingCover_of_boxTrifurcation n h

/--
[bc21_burtonKeane_uniqueness_of_boxTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_burtonKeane_uniqueness_of_boxTrifurcation_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hr : ∀ n : ℕ, bc12_BoxOriginTrifurcation d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc21_burtonKeane_uniqueness_of_boxTrifurcation μ herg hfe bdry hbound hvol hdens hr

/--
[bc21_px0_eq_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_px0_eq_origin_eq
  {d : ℕ} :
-- imply
  px 0 = (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc21_px0_eq_origin

/--
[bc21_threeRay_trif_at_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_threeRay_trif_at_origin_eq
  {d : ℕ} :
-- imply
  IsCanonicalTrifurcation 2 threeRayConfig 0 := by
-- proof
  apply StatMech.Walls.bc21_threeRay_trif_at_origin

/--
[bc21_originBranchSurvivalCut_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_originBranchSurvivalCut_nonvacuous_eq
  {d : ℕ} :
-- imply
  ∃ ω : ConfigSpace (Sym2 (Site 2)), bc21_OriginBranchSurvivalCut 2 ω := by
-- proof
  apply StatMech.Walls.bc21_originBranchSurvivalCut_nonvacuous

/--
[bc21_mengerCore_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc21trifurc.lean)
-/
@[path]
private lemma bc21_mengerCore_nonvacuous_eq
  {d : ℕ} :
-- imply
  ∃ ω : ConfigSpace (Sym2 (Site 2)), MengerCore ω := by
-- proof
  apply StatMech.Walls.bc21_mengerCore_nonvacuous


-- created on 2026-10-23
