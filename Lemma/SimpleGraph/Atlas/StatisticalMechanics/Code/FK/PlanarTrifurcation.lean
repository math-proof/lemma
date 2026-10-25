import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PlanarTrifurcation
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls StatMech.Percolation StatMech.FK


/--
[bins_exists_NineShellEvent_pos_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma bins_exists_NineShellEvent_pos_measure_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure mu]
-- given
  (htop : 0 < mu {omega | numInfiniteClusters 2 omega = ⊤}) :
-- imply
  ∃ (n : ℕ) (v u : Fin 9 → Site 2), 0 < mu (bins_NineShellEvent n v u) := by
-- proof
  apply StatMech.Walls.bins_exists_NineShellEvent_pos_measure mu htop

/--
[bins_setPattern_preimage_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma bins_setPattern_preimage_inter_eq
  {I : Finset (Sym2 (Site 2))}
  {eta : ConfigSpace ↥I}
  {X : Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hX : DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ)) :
-- imply
  setPattern I eta ⁻¹' (cylinder I ({eta} : Set (ConfigSpace ↥I)) ∩ X) = X := by
-- proof
  apply StatMech.Walls.bins_setPattern_preimage_inter I eta X hX

/--
[bins_precursor_pos_of_patternAC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma bins_precursor_pos_of_patternAC_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure mu]
-- given
  (hpattern : ∀ (I : Finset (Sym2 (Site 2))) (eta : ConfigSpace ↥I), mu.map (setPattern I eta) ≪ mu)
  (htop : 0 < mu {omega | numInfiniteClusters 2 omega = ⊤}) :
-- imply
  ∃ a1 a2 a3 : Site 2, 0 < mu (NeighborTrifPrecursor 2 a1 a2 a3) := by
-- proof
  apply StatMech.Walls.bins_precursor_pos_of_patternAC mu hpattern htop

/--
[precursor_subset_force_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma precursor_subset_force_canonical_eq
  {a1 a2 a3 : Site d} :
-- imply
  NeighborTrifPrecursor d a1 a2 a3 ⊆ (fun omega => forceOpenFinset {s((0 : Site d), a1), s((0 : Site d), a2), s((0 : Site d), a3)} omega) ⁻¹' {omega | IsCanonicalTrifurcation d omega 0} := by
-- proof
  apply StatMech.Percolation.precursor_subset_force_canonical a1 a2 a3

/--
[canonicalTrif_pos_of_precursor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma canonicalTrif_pos_of_precursor_pos_eq
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
  {a1 a2 a3 : Site d}
-- given
  (hfe : HasFiniteEnergyMerge mu)
  (hpos : 0 < mu (NeighborTrifPrecursor d a1 a2 a3)) :
-- imply
  0 < mu {omega | IsCanonicalTrifurcation d omega 0} := by
-- proof
  apply StatMech.Percolation.canonicalTrif_pos_of_precursor_pos mu hfe a1 a2 a3 hpos

/--
[wiredInfinite_planar_canonicalTrif_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma wiredInfinite_planar_canonicalTrif_pos_of_top_pos_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htop : 0 < (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters 2 omega = ⊤}) :
-- imply
  0 < (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | IsCanonicalTrifurcation 2 omega 0} := by
-- proof
  apply StatMech.FK.wiredInfinite_planar_canonicalTrif_pos_of_top_pos hp hp1 hq htop

/--
[freeInfinite_planar_canonicalTrif_pos_of_top_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma freeInfinite_planar_canonicalTrif_pos_of_top_pos_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (htop : 0 < (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters 2 omega = ⊤}) :
-- imply
  0 < (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | IsCanonicalTrifurcation 2 omega 0} := by
-- proof
  apply StatMech.FK.freeInfinite_planar_canonicalTrif_pos_of_top_pos hp hp1 hq htop

/--
[wiredInfinite_planar_canonical_uniqueness_of_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma wiredInfinite_planar_canonical_uniqueness_of_ergodic_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (herg : IsErgodic (G := Multiplicative (Site 2)) (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2))))) :
-- imply
  ((wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters 2 omega = 0} = 1 ∨ (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters 2 omega = 1} = 1) ∧ (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) (atLeastTwoInfinite 2) = 0 ∧ (wiredInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters 2 omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FK.wiredInfinite_planar_canonical_uniqueness_of_ergodic hp hp1 hq herg

/--
[freeInfinite_planar_canonical_uniqueness_of_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma freeInfinite_planar_canonical_uniqueness_of_ergodic_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (herg : IsErgodic (G := Multiplicative (Site 2)) (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2))))) :
-- imply
  ((freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters 2 omega = 0} = 1 ∨ (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters 2 omega = 1} = 1) ∧ (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) (atLeastTwoInfinite 2) = 0 ∧ (freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | numInfiniteClusters 2 omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FK.freeInfinite_planar_canonical_uniqueness_of_ergodic hp hp1 hq herg

/--
[wiredInfinite_planar_q2_canonical_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlanarTrifurcation.lean)
-/
@[path]
private lemma wiredInfinite_planar_q2_canonical_uniqueness_eq
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ((wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters 2 omega = 0} = 1 ∨ (wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters 2 omega = 1} = 1) ∧ (wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) (atLeastTwoInfinite 2) = 0 ∧ (wiredInfiniteVolume 2 hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | numInfiniteClusters 2 omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FK.wiredInfinite_planar_q2_canonical_uniqueness hp hp1


-- created on 2026-10-23
