import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedBounds
open StatMech StatMech.Onsager


/--
[norm_ons_KWmatWeightedPhase_entry_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBounds.lean)
-/
@[path]
private lemma norm_ons_KWmatWeightedPhase_entry_le_eq
  {L : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
  {q : ℝ}
  {d2 d1 : ons_Dart L}
-- given
  (hq : 0 ≤ q)
  (hweight : ∀ edge, ‖weight edge‖ ≤ q) :
-- imply
  ‖ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖ ≤ q := by
-- proof
  apply StatMech.Onsager.norm_ons_KWmatWeightedPhase_entry_le L weight a b q hq hweight d2 d1

/--
[ons_card_mul_lt_one_of_Sherman_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBounds.lean)
-/
@[path]
private lemma ons_card_mul_lt_one_of_Sherman_small_eq
  [Fintype E]
  [Nonempty E]
  {q : ℝ}
-- given
  (hsmall : q < (2 * (Fintype.card E : ℝ) ^ 2)⁻¹) :
-- imply
  (Fintype.card E : ℝ) * q < 1 := by
-- proof
  apply StatMech.Onsager.ons_card_mul_lt_one_of_Sherman_small q hsmall

/--
[ons_matrix_norm_le_of_entry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBounds.lean)
-/
@[path]
private lemma ons_matrix_norm_le_of_entry_eq
  [Fintype E]
  [DecidableEq E]
  {A : Matrix E E ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖A i j‖ ≤ q) :
-- imply
  letI : NormedRing (Matrix E E ℂ) := Matrix.linftyOpNormedRing ‖A‖ ≤ (Fintype.card E : ℝ) * q := by
-- proof
  apply StatMech.Onsager.ons_matrix_norm_le_of_entry A q hq hentry

/--
[ons_spectral_lt_one_of_entry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBounds.lean)
-/
@[path]
private lemma ons_spectral_lt_one_of_entry_eq
  [Fintype E]
  [DecidableEq E]
  {A : Matrix E E ℂ}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hentry : ∀ i j, ‖A i j‖ ≤ q)
  (hcard : (Fintype.card E : ℝ) * q < 1) :
-- imply
  ∀ alpha ∈ A.charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_spectral_lt_one_of_entry A q hq hentry hcard

/--
[ons_KWmatWeightedPhase_detWalkRoot_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedBounds.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_detWalkRoot_sq_eq
  {L : ℕ}
  [NeZero L]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
  {q : ℝ}
-- given
  (hq : 0 ≤ q)
  (hweight : ∀ edge, ‖weight edge‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹) :
-- imply
  ons_detWalkRoot (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) ^ 2 = (1 - ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_detWalkRoot_sq L weight a b q hq hweight hsmall


-- created on 2026-10-23
