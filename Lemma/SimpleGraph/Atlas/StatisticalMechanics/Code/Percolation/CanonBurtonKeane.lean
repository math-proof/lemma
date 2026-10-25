import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.CanonBurtonKeane
open StatMech StatMech.Percolation


/--
[cbk_boundary_succ_vol_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonBurtonKeane.lean)
-/
@[path]
private lemma cbk_boundary_succ_vol_tendsto_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Percolation.cbk_boundary_succ_vol_tendsto d hd

/--
[cbk_canonical_trif_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonBurtonKeane.lean)
-/
@[path]
private lemma cbk_canonical_trif_prob_eq_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  μ {ω | IsCanonicalTrifurcation d ω 0} = 0 := by
-- proof
  apply StatMech.Percolation.cbk_canonical_trif_prob_eq_zero μ hd hinv

/--
[cbk_numInfiniteClusters_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonBurtonKeane.lean)
-/
@[path]
private lemma cbk_numInfiniteClusters_ne_top_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsCanonicalTrifurcation d ω 0}) :
-- imply
  ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
-- proof
  apply StatMech.Percolation.cbk_numInfiniteClusters_ne_top μ hd herg htrif

/--
[cbk_canonical_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonBurtonKeane.lean)
-/
@[path]
private lemma cbk_canonical_uniqueness_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsCanonicalTrifurcation d ω 0}) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.cbk_canonical_uniqueness μ hd herg hfe htrif


-- created on 2026-10-23
