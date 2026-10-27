import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
open MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[removeSite_apply_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma removeSite_apply_of_mem_eq
  {d : ℕ}
  {x : Site d}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : x ∈ e) :
-- imply
  removeSite x ω e = false := by
-- proof
  apply StatMech.Percolation.removeSite_apply_of_mem h ω

/--
[removeSite_apply_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma removeSite_apply_of_notMem_eq
  {d : ℕ}
  {x : Site d}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : x ∉ e) :
-- imply
  removeSite x ω e = ω e := by
-- proof
  apply StatMech.Percolation.removeSite_apply_of_notMem h ω

/--
[measurable_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma measurable_removeSite_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => removeSite x ω) := by
-- proof
  apply StatMech.Percolation.measurable_removeSite x

/--
[removeSite_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma removeSite_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSite (g • x) (shift g ω) = shift g (removeSite x ω) := by
-- proof
  apply StatMech.Percolation.removeSite_shift g x ω

/--
[measurableSet_connected_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma measurableSet_connected_removeSite_eq
  {d : ℕ}
  {x a b : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSite x ω) a b} := by
-- proof
  apply StatMech.Percolation.measurableSet_connected_removeSite x a b

/--
[measurableSet_isTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma measurableSet_isTrifurcation_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | IsTrifurcation d ω x} := by
-- proof
  apply StatMech.Percolation.measurableSet_isTrifurcation x

/--
[isTrifurcation_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma isTrifurcation_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  IsTrifurcation d (shift g ω) (g • x) ↔ IsTrifurcation d ω x := by
-- proof
  apply StatMech.Percolation.isTrifurcation_shift g ω x

/--
[trifurcationProb_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma trifurcationProb_const_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {x : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  μ {ω | IsTrifurcation d ω x} = μ {ω | IsTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.trifurcationProb_const μ hinv x

/--
[Tcount_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma Tcount_eq_sum_indicator_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  (Tcount d ω n : ℝ≥0∞) = ∑ x ∈ boxFinsetBK d n, ({ω' | IsTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
-- proof
  apply StatMech.Percolation.Tcount_eq_sum_indicator ω n

/--
[expected_Tcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma expected_Tcount_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {n : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ∫⁻ ω, (Tcount d ω n : ℝ≥0∞) ∂μ = (boxFinsetBK d n).card • μ {ω | IsTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.expected_Tcount μ hinv n

/--
[trifurcation_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma trifurcation_prob_eq_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  μ {ω | IsTrifurcation d ω 0} = 0 := by
-- proof
  apply StatMech.Percolation.trifurcation_prob_eq_zero μ hinv bdry hbound hvol hdens

/--
[numInfiniteClusters_ae_const_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma numInfiniteClusters_ae_const_uniqueness_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ) :
-- imply
  ∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_ae_const_uniqueness μ herg

/--
[numInfiniteClusters_ae_const_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneUniqueness.lean)
-/
@[path]
private lemma numInfiniteClusters_ae_const_ne_top_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0}) :
-- imply
  ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_ae_const_ne_top μ herg bdry hbound hvol hdens htrif


-- created on 2026-10-23
