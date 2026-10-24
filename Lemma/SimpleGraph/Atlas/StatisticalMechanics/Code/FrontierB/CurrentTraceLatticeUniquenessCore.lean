import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentTraceLatticeUniquenessCore
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[boxEdges_subset_hypercubic_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceLatticeUniquenessCore.lean)
-/
@[path]
private lemma boxEdges_subset_hypercubic_edgeSet_eq
  {d n : ℕ} :
-- imply
  (↑(boxEdges d n) : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.boxEdges_subset_hypercubic_edgeSet d n

/--
[latticeInsertionMerge_excludes_finite_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceLatticeUniquenessCore.lean)
-/
@[path]
private lemma latticeInsertionMerge_excludes_finite_ge_two_eq
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hfe : ∀ F : Finset (Sym2 (Site d)), (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet → μ.map (fun ω => forceOpenFinset F ω) ≪ μ)
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
  (hk2 : 2 ≤ k)
  (hktop : k ≠ ⊤) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierB.latticeInsertionMerge_excludes_finite_ge_two μ hfe hk hk2 hktop

/--
[latticeInsertion_canonical_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceLatticeUniquenessCore.lean)
-/
@[path]
private lemma latticeInsertion_canonical_uniqueness_eq
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : ∀ F : Finset (Sym2 (Site d)), (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet → μ.map (fun ω => forceOpenFinset F ω) ≪ μ)
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsCanonicalTrifurcation d ω 0}) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.latticeInsertion_canonical_uniqueness μ hd herg hfe htrif


-- created on 2026-10-23
