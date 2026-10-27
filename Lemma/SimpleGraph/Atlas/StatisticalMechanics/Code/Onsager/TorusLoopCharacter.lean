import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopCharacter.Part2
open StatMech StatMech.Onsager


/--
[ons_neg_one_zpow_eq_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean)
-/
@[path]
private lemma ons_neg_one_zpow_eq_parity_eq
  {m : ℤ} :
-- imply
  (-1 : ℂ) ^ m = (-1 : ℂ) ^ (ons_intParity m).val := by
-- proof
  apply StatMech.Onsager.ons_neg_one_zpow_eq_parity m

/--
[ons_spinPhase_character](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean)
-/
@[path]
private lemma ons_spinPhase_character_eq
  {a b : Fin 2}
  {mx my : ℤ} :
-- imply
  (-1 : ℂ) ^ ((a.val : ℤ) * mx + (b.val : ℤ) * my) = ons_spinLinearCharacter a b (ons_windingParity mx my) := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_character a b mx my

/--
[ons_spinLinear_mul_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean)
-/
@[path]
private lemma ons_spinLinear_mul_quadratic_eq
  {a b : Fin 2}
-- given
  (h : Fin 2 × Fin 2) :
-- imply
  ons_spinLinearCharacter a b h * (ons_spinCharacter 0 0 h : ℂ) = (ons_spinCharacter a b h : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_spinLinear_mul_quadratic a b h

/--
[ons_loopWeight_spinPhase_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean)
-/
@[path]
private lemma ons_loopWeight_spinPhase_of_winding_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my) :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d = (-1 : ℂ) ^ ((a.val : ℤ) * mx + (b.val : ℤ) * my) * ons_loopWeight (ons_KWmat L x omega) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_spinPhase_of_winding x omega a b d mx my hmx hmy

/--
[ons_loopWeight_eq_spinCharacter_of_geometric_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopCharacter.lean)
-/
@[path]
private lemma ons_loopWeight_eq_spinCharacter_of_geometric_sign_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my)
  (hgeom : ons_loopWeight (ons_KWmat L x omega) d = -(ons_spinCharacter 0 0 (ons_windingParity mx my) : ℂ) * x ^ n) :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d = -(ons_spinCharacter a b (ons_windingParity mx my) : ℂ) * x ^ n := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_eq_spinCharacter_of_geometric_sign x omega a b d mx my hmx hmy hgeom


-- created on 2026-10-23
