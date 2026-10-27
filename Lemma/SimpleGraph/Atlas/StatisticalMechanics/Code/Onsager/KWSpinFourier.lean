import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part3
open StatMech StatMech.Onsager


/--
[ons_dirPhase_eq_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_dirPhase_eq_zpow_eq
  {u v : ℂ}
  {mu : Fin 4} :
-- imply
  ons_dirPhase u v mu = u ^ ons_dirExponentX mu * v ^ ons_dirExponentY mu := by
-- proof
  apply StatMech.Onsager.ons_dirPhase_eq_zpow u v mu

/--
[prod_ons_dirPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma prod_ons_dirPhase_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {u v : ℂ}
  {d : alpha → Fin 4}
-- given
  (hu : u ≠ 0)
  (hv : v ≠ 0) :
-- imply
  (∏ i, ons_dirPhase u v (d i)) = u ^ (∑ i, ons_dirExponentX (d i)) * v ^ (∑ i, ons_dirExponentY (d i)) := by
-- proof
  apply StatMech.Onsager.prod_ons_dirPhase u v hu hv d

/--
[ons_KWmatPhase_translation_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_KWmatPhase_translation_invariant_eq
  {L : ℕ}
  {x omega u v : ℂ}
  {t : ZMod L × ZMod L}
  {d1 d2 : ons_Dart L} :
-- imply
  ons_KWmatPhase L x omega u v (ons_shiftDart L t d2) (ons_shiftDart L t d1) = ons_KWmatPhase L x omega u v d2 d1 := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_translation_invariant L x omega u v t d1 d2

/--
[ons_KWmatPhase_eq_blockCirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_KWmatPhase_eq_blockCirc_eq
  {L : ℕ}
  {x omega u v : ℂ} :
-- imply
  ons_KWmatPhase L x omega u v = ons_blockCirculant2D L 4 (ons_KWblockPhase L x omega u v) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_eq_blockCirc L x omega u v

/--
[ons_KWblockPhaseSymbol_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_KWblockPhaseSymbol_eq_eq
  {L : ℕ}
  [NeZero L]
  [Fact (1 < L)]
  {x omega u v root : ℂ}
  {j : ZMod L × ZMod L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hroot : IsPrimitiveRoot root L)
  (hu : u ≠ 0)
  (hv : v ≠ 0) :
-- imply
  ons_blockSymbol2D L 4 root (fun g => (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) - ons_KWblockPhase L x omega u v g) j = ons_KWsymbolMat x omega (u * root ^ j.1.val) (v * root ^ j.2.val) := by
-- proof
  apply StatMech.Onsager.ons_KWblockPhaseSymbol_eq L x omega u v root homega hroot hu hv j

/--
[ons_KWmatPhase_det_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_KWmatPhase_det_eq_prod_eq
  {L : ℕ}
  [NeZero L]
  [Fact (1 < L)]
  {x omega u v root : ℂ}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hroot : IsPrimitiveRoot root L)
  (hu : u ≠ 0)
  (hv : v ≠ 0) :
-- imply
  (1 - ons_KWmatPhase L x omega u v).det = ∏ j : ZMod L × ZMod L, ((1 + x ^ 2) ^ 2 - x * (1 - x ^ 2) * (u * root ^ j.1.val + (u * root ^ j.1.val)⁻¹ + (v * root ^ j.2.val + (v * root ^ j.2.val)⁻¹))) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_det_eq_prod L x omega u v root homega hroot hu hv

/--
[ons_spinPhase_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_spinPhase_ne_zero_eq
  {L : ℕ}
  {a : Fin 2} :
-- imply
  ons_spinPhase L a ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_ne_zero L a

/--
[ons_spinPhase_pow_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_spinPhase_pow_side_eq
  {L : ℕ}
  [NeZero L]
  {a : Fin 2} :
-- imply
  ons_spinPhase L a ^ L = (-1 : ℂ) ^ a.val := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_pow_side L a

/--
[ons_spinPhase_mul_spaceRoot_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_spinPhase_mul_spaceRoot_pow_eq
  {L m : ℕ}
  {a : Fin 2} :
-- imply
  ons_spinPhase L a * ons_spaceRoot L ^ m = Complex.exp (Complex.I * ((2 * Real.pi * (m + (a.val : ℝ) / 2) / L : ℝ) : ℂ)) := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_mul_spaceRoot_pow L m a

/--
[ons_spinPhase_spaceRoot_cos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_spinPhase_spaceRoot_cos_eq
  {L m : ℕ}
  {a : Fin 2} :
-- imply
  ons_spinPhase L a * ons_spaceRoot L ^ m + (ons_spinPhase L a * ons_spaceRoot L ^ m)⁻¹ = 2 * (Real.cos (2 * Real.pi * (m + (a.val : ℝ) / 2) / L) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_spaceRoot_cos L m a

/--
[prod_zmod_prod_eq_prod_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma prod_zmod_prod_eq_prod_range_eq
  {L : ℕ}
  [NeZero L]
  {F : ℕ → ℕ → ℂ} :
-- imply
  (∏ j : ZMod L × ZMod L, F j.1.val j.2.val) = ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L, F i j := by
-- proof
  apply StatMech.Onsager.prod_zmod_prod_eq_prod_range L F

/--
[ons_KWmatPhase_det_eq_spinDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean)
-/
@[path]
private lemma ons_KWmatPhase_det_eq_spinDet_eq
  {L : ℕ}
  [NeZero L]
  [Fact (1 < L)]
  {beta : ℝ}
  {a b : Fin 2} :
-- imply
  (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det = (ons_spinDet L beta a b : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_det_eq_spinDet L beta a b


-- created on 2026-10-23
