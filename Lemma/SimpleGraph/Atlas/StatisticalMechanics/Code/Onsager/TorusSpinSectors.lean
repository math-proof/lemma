import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3
open StatMech StatMech.Onsager


/--
[ons_evenHomology_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_evenHomology_union_eq
  {L : ℕ}
  {F G : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hdisj : Disjoint F G) :
-- imply
  ons_evenHomology L (F ∪ G) = ons_evenHomology L F + ons_evenHomology L G := by
-- proof
  apply StatMech.Onsager.ons_evenHomology_union L F G hdisj

/--
[ons_evenHomology_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_evenHomology_biUnion_eq
  {L : ℕ}
  [DecidableEq iota]
  {S : Finset iota}
  {piece : iota → Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hdisj : (S : Set iota).PairwiseDisjoint piece) :
-- imply
  ons_evenHomology L (S.biUnion piece) = ∑ i ∈ S, ons_evenHomology L (piece i) := by
-- proof
  apply StatMech.Onsager.ons_evenHomology_biUnion S piece hdisj

/--
[ons_X_eq_sum_sectorWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_X_eq_sum_sectorWeight_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  ons_X (onsTorusGraph L) x = ∑ h : Fin 2 × Fin 2, ons_sectorWeight L x h := by
-- proof
  apply StatMech.Onsager.ons_X_eq_sum_sectorWeight L x

/--
[ons_X_eq_sector_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_X_eq_sector_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  ons_X (onsTorusGraph L) x = ons_sector00 L x + ons_sector10 L x + ons_sector01 L x + ons_sector11 L x := by
-- proof
  apply StatMech.Onsager.ons_X_eq_sector_sum L x

/--
[ons_two_mul_X_eq_spin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_two_mul_X_eq_spin_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  2 * ons_X (onsTorusGraph L) x = ons_spin00 L x + ons_spin10 L x + ons_spin01 L x - ons_spin11 L x := by
-- proof
  apply StatMech.Onsager.ons_two_mul_X_eq_spin_sum L x

/--
[ons_sectorWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_sectorWeight_nonneg_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
-- given
  (hx : 0 ≤ x)
  (h : Fin 2 × Fin 2) :
-- imply
  0 ≤ ons_sectorWeight L x h := by
-- proof
  apply StatMech.Onsager.ons_sectorWeight_nonneg L hx h

/--
[ons_sectorWeight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_sectorWeight_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (h : Fin 2 × Fin 2) :
-- imply
  ons_sectorWeight L 0 h = if h = (0, 0) then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_sectorWeight_zero L h

/--
[ons_abs_spin_le_X](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_abs_spin_le_X_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  |ons_spin00 L x| ≤ ons_X (onsTorusGraph L) x ∧ |ons_spin10 L x| ≤ ons_X (onsTorusGraph L) x ∧ |ons_spin01 L x| ≤ ons_X (onsTorusGraph L) x ∧ |ons_spin11 L x| ≤ ons_X (onsTorusGraph L) x := by
-- proof
  apply StatMech.Onsager.ons_abs_spin_le_X L hx

/--
[ons_two_mul_X_le_sum_abs_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean)
-/
@[path]
private lemma ons_two_mul_X_le_sum_abs_spin_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  2 * ons_X (onsTorusGraph L) x ≤ |ons_spin00 L x| + |ons_spin10 L x| + |ons_spin01 L x| + |ons_spin11 L x| := by
-- proof
  apply StatMech.Onsager.ons_two_mul_X_le_sum_abs_spin L x


-- created on 2026-10-23
