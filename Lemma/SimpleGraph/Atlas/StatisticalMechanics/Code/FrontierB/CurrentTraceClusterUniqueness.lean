import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.CurrentTraceClusterUniqueness
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[latticeFiniteEnergyMerge_excludes_finite_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceClusterUniqueness.lean)
-/
@[path]
private lemma latticeFiniteEnergyMerge_excludes_finite_ge_two_eq
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hfe : HasLatticeFiniteEnergyMerge μ)
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
  (hk2 : 2 ≤ k)
  (hktop : k ≠ ⊤) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierB.latticeFiniteEnergyMerge_excludes_finite_ge_two μ hfe hk hk2 hktop

/--
[latticeFiniteEnergy_canonical_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceClusterUniqueness.lean)
-/
@[path]
private lemma latticeFiniteEnergy_canonical_uniqueness_eq
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasLatticeFiniteEnergyMerge μ)
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsCanonicalTrifurcation d ω 0}) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.latticeFiniteEnergy_canonical_uniqueness μ hd herg hfe htrif

/--
[freeFreeSuperposedTraceLaw_canonical_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceClusterUniqueness.lean)
-/
@[path]
private lemma freeFreeSuperposedTraceLaw_canonical_uniqueness_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))))
  (htrif : 0 < (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) {ω | numInfiniteClusters d ω = ⊤} → 0 < (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) {ω | IsCanonicalTrifurcation d ω 0}) :
-- imply
  let μ := (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.freeFreeSuperposedTraceLaw_canonical_uniqueness d beta hbeta hd herg htrif

/--
[freePlusSuperposedTraceLaw_canonical_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceClusterUniqueness.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_canonical_uniqueness_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))))
  (htrif : 0 < (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) {ω | numInfiniteClusters d ω = ⊤} → 0 < (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) {ω | IsCanonicalTrifurcation d ω 0}) :
-- imply
  let μ := (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_canonical_uniqueness d beta hbeta hd herg htrif

/--
[plusPlusSuperposedTraceLaw_canonical_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceClusterUniqueness.lean)
-/
@[path]
private lemma plusPlusSuperposedTraceLaw_canonical_uniqueness_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))))
  (htrif : 0 < (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) {ω | numInfiniteClusters d ω = ⊤} → 0 < (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) {ω | IsCanonicalTrifurcation d ω 0}) :
-- imply
  let μ := (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.plusPlusSuperposedTraceLaw_canonical_uniqueness d beta hbeta hd herg htrif


-- created on 2026-10-23
