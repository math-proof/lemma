import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.KWSpectralSharp
open StatMech StatMech.Onsager


/--
[ons_turnRoot_conj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma ons_turnRoot_conj_eq :
-- imply
  star ons_turnRoot = ons_turnRoot⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_turnRoot_conj

/--
[ons_turnRoot_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma ons_turnRoot_ne_zero_eq :
-- imply
  ons_turnRoot ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_turnRoot_ne_zero

/--
[ons_turnMatrix_turnRoot_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma ons_turnMatrix_turnRoot_isHermitian_eq :
-- imply
  (ons_turnMatrix ons_turnRoot).IsHermitian := by
-- proof
  apply StatMech.Onsager.ons_turnMatrix_turnRoot_isHermitian

/--
[ons_turnMatrix_centered_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma ons_turnMatrix_centered_sq_eq :
-- imply
  (ons_turnMatrix ons_turnRoot - 1) * (ons_turnMatrix ons_turnRoot - 1) = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
-- proof
  apply StatMech.Onsager.ons_turnMatrix_centered_sq

/--
[ons_arrivalTurnMatrix_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma ons_arrivalTurnMatrix_isHermitian_eq
  {L : ℕ} :
-- imply
  (ons_arrivalTurnMatrix L).IsHermitian := by
-- proof
  apply StatMech.Onsager.ons_arrivalTurnMatrix_isHermitian L

/--
[ons_arrivalTurnMatrix_centered_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma ons_arrivalTurnMatrix_centered_apply_eq
  {L : ℕ}
  {d2 d1 : ons_Dart L} :
-- imply
  (ons_arrivalTurnMatrix L - 1) d2 d1 = if d2.1 = d1.1 then (ons_turnMatrix ons_turnRoot - 1) d2.2 d1.2 else 0 := by
-- proof
  apply StatMech.Onsager.ons_arrivalTurnMatrix_centered_apply L d2 d1

/--
[ons_arrivalTurnMatrix_centered_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma ons_arrivalTurnMatrix_centered_sq_eq
  {L : ℕ}
  [NeZero L] :
-- imply
  (ons_arrivalTurnMatrix L - 1) * (ons_arrivalTurnMatrix L - 1) = (2 : ℂ) • (1 : Matrix (ons_Dart L) (ons_Dart L) ℂ) := by
-- proof
  apply StatMech.Onsager.ons_arrivalTurnMatrix_centered_sq L

/--
[ons_KWmat_eq_arrivalTurn_mul_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma ons_KWmat_eq_arrivalTurn_mul_perm_eq
  {L : ℕ}
  [NeZero L] :
-- imply
  ons_KWmat L 1 ons_turnRoot = ons_arrivalTurnMatrix L * (ons_tailDartEquiv L).permMatrix ℂ := by
-- proof
  apply StatMech.Onsager.ons_KWmat_eq_arrivalTurn_mul_perm L

/--
[norm_ons_turnMatrix_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma norm_ons_turnMatrix_centered_eq :
-- imply
  letI : NormedRing (Matrix (Fin 4) (Fin 4) ℂ) := Matrix.instL2OpNormedRing ‖ons_turnMatrix ons_turnRoot - 1‖ = Real.sqrt 2 := by
-- proof
  apply StatMech.Onsager.norm_ons_turnMatrix_centered

/--
[norm_ons_arrivalTurnMatrix_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma norm_ons_arrivalTurnMatrix_centered_eq
  {L : ℕ}
  [NeZero L] :
-- imply
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) := Matrix.instL2OpNormedRing ‖ons_arrivalTurnMatrix L - 1‖ = Real.sqrt 2 := by
-- proof
  apply StatMech.Onsager.norm_ons_arrivalTurnMatrix_centered L

/--
[norm_ons_arrivalTurnMatrix_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma norm_ons_arrivalTurnMatrix_le_eq
  {L : ℕ}
  [NeZero L] :
-- imply
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) := Matrix.instL2OpNormedRing ‖ons_arrivalTurnMatrix L‖ ≤ Real.sqrt 2 + 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_arrivalTurnMatrix_le L

/--
[norm_ons_KWmat_turnRoot_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralSharp.lean)
-/
@[path]
private lemma norm_ons_KWmat_turnRoot_sharp_eq
  {L : ℕ}
  [NeZero L]
  {x : ℂ} :
-- imply
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) := Matrix.instL2OpNormedRing ‖ons_KWmat L x ons_turnRoot‖ ≤ (Real.sqrt 2 + 1) * ‖x‖ := by
-- proof
  apply StatMech.Onsager.norm_ons_KWmat_turnRoot_sharp L x


-- created on 2026-10-23
