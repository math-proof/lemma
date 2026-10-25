import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationPatternMeasure
open Set MeasureTheory Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[threeMeetBox_subset_pattern_trifurcations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationPatternMeasure.lean)
-/
@[path]
private lemma threeMeetBox_subset_pattern_trifurcations_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  threeMeetBox d n ⊆ ⋃ eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n), ⋃ hub : Site d, StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta ⁻¹' {omega | IsTrifurcation d omega hub} := by
-- proof
  apply StatMech.Percolation.threeMeetBox_subset_pattern_trifurcations n

/--
[threeMeetBox_subset_pattern_canonical_trifurcations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationPatternMeasure.lean)
-/
@[path]
private lemma threeMeetBox_subset_pattern_canonical_trifurcations_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  threeMeetBox d n ⊆ ⋃ eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n), ⋃ hub : Site d, StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta ⁻¹' {omega | IsCanonicalTrifurcation d omega hub} := by
-- proof
  apply StatMech.Percolation.threeMeetBox_subset_pattern_canonical_trifurcations n

/--
[trifurcation_pos_of_threeMeetBox_patternAC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationPatternMeasure.lean)
-/
@[path]
private lemma trifurcation_pos_of_threeMeetBox_patternAC_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
  {n : ℕ}
-- given
  (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I), mu.map (StatMech.FK.setPattern I eta) ≪ mu)
  (hpos : 0 < mu (threeMeetBox d n)) :
-- imply
  ∃ hub : Site d, 0 < mu {omega | IsTrifurcation d omega hub} := by
-- proof
  apply StatMech.Percolation.trifurcation_pos_of_threeMeetBox_patternAC mu hpattern n hpos

/--
[canonical_trifurcation_pos_of_threeMeetBox_patternAC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationPatternMeasure.lean)
-/
@[path]
private lemma canonical_trifurcation_pos_of_threeMeetBox_patternAC_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
  {n : ℕ}
-- given
  (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I), mu.map (StatMech.FK.setPattern I eta) ≪ mu)
  (hpos : 0 < mu (threeMeetBox d n)) :
-- imply
  ∃ hub : Site d, 0 < mu {omega | IsCanonicalTrifurcation d omega hub} := by
-- proof
  apply StatMech.Percolation.canonical_trifurcation_pos_of_threeMeetBox_patternAC mu hpattern n hpos

/--
[trifurcation_at_origin_pos_of_patternAC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationPatternMeasure.lean)
-/
@[path]
private lemma trifurcation_at_origin_pos_of_patternAC_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
  (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I), mu.map (StatMech.FK.setPattern I eta) ≪ mu)
  (htop : 0 < mu {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < mu {omega | IsTrifurcation d omega 0} := by
-- proof
  apply StatMech.Percolation.trifurcation_at_origin_pos_of_patternAC mu hinv hpattern htop

/--
[canonical_trifurcation_at_origin_pos_of_patternAC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationPatternMeasure.lean)
-/
@[path]
private lemma canonical_trifurcation_at_origin_pos_of_patternAC_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
  (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I), mu.map (StatMech.FK.setPattern I eta) ≪ mu)
  (htop : 0 < mu {omega | numInfiniteClusters d omega = ⊤}) :
-- imply
  0 < mu {omega | IsCanonicalTrifurcation d omega 0} := by
-- proof
  apply StatMech.Percolation.canonical_trifurcation_at_origin_pos_of_patternAC mu hinv hpattern htop


-- created on 2026-10-23
