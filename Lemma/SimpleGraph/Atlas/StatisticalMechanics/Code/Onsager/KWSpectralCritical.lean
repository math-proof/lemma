import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
open StatMech StatMech.Onsager


/--
[ons_KWmatWeightedPhase_eq_unit_mul_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_eq_unit_mul_diagonal_eq
  {L : Nat}
  [NeZero L]
  {a b : Fin 2}
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
-- imply
  ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) = ons_KWmat L 1 ons_turnRoot * Matrix.diagonal (ons_KWcolumnMultiplier L weight a b) := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_eq_unit_mul_diagonal L weight a b

/--
[norm_ons_KWcolumnMultiplier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma norm_ons_KWcolumnMultiplier_le_eq
  {L : Nat}
  {a b : Fin 2}
  {dart : ons_Dart L}
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
-- imply
  ‖ons_KWcolumnMultiplier L weight a b dart‖ <= ‖weight (ons_portEdge L dart)‖ := by
-- proof
  apply StatMech.Onsager.norm_ons_KWcolumnMultiplier_le L weight a b dart

/--
[norm_diagonal_ons_KWcolumnMultiplier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma norm_diagonal_ons_KWcolumnMultiplier_le_eq
  {L : Nat}
  [NeZero L]
  {a b : Fin 2}
  {q : Real}
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Complex)
  (hweight : forall edge, ‖weight edge‖ <= q) :
-- imply
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) Complex) := Matrix.instL2OpNormedRing ‖Matrix.diagonal (ons_KWcolumnMultiplier L weight a b)‖ <= q := by
-- proof
  apply StatMech.Onsager.norm_diagonal_ons_KWcolumnMultiplier_le L weight a b q hweight

/--
[norm_ons_KWmatWeightedPhase_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma norm_ons_KWmatWeightedPhase_sharp_eq
  {L : Nat}
  [NeZero L]
  {a b : Fin 2}
  {q : Real}
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Complex)
  (hweight : forall edge, ‖weight edge‖ <= q) :
-- imply
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) Complex) := Matrix.instL2OpNormedRing ‖ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)‖ <= (Real.sqrt 2 + 1) * q := by
-- proof
  apply StatMech.Onsager.norm_ons_KWmatWeightedPhase_sharp L weight a b q hweight

/--
[norm_root_ons_KWmatWeightedPhase_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma norm_root_ons_KWmatWeightedPhase_le_eq
  {L : Nat}
  [NeZero L]
  {a b : Fin 2}
  {q : Real}
  {alpha : Complex}
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Complex)
  (hweight : forall edge, ‖weight edge‖ <= q)
  (halpha : alpha ∈ (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots) :
-- imply
  ‖alpha‖ <= (Real.sqrt 2 + 1) * q := by
-- proof
  apply StatMech.Onsager.norm_root_ons_KWmatWeightedPhase_le L weight a b q hweight alpha halpha

/--
[ons_KWmatWeightedPhase_spectral_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_spectral_critical_eq
  {L : Nat}
  [NeZero L]
  {a b : Fin 2}
  {q : Real}
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Complex)
  (hq : q < ons_signedLoopCriticalWeight)
  (hweight : forall edge, ‖weight edge‖ <= q) :
-- imply
  ∀ alpha ∈ (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_spectral_critical L weight a b q hq hweight

/--
[ons_KWmatWeightedPhase_det_eq_walk_exp_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_det_eq_walk_exp_critical_eq
  {L : Nat}
  [NeZero L]
  {a b : Fin 2}
  {q : Real}
-- given
  (weight : Sym2 (ZMod L × ZMod L) -> Complex)
  (hq : q < ons_signedLoopCriticalWeight)
  (hweight : forall edge, ‖weight edge‖ <= q) :
-- imply
  (1 - ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det = Complex.exp (- ∑' n : Nat, (∑ v : Fin (n + 1) -> ons_Dart L, ∏ k : Fin (n + 1), ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (v k) (v (k + 1))) / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_det_eq_walk_exp_critical L weight a b q hq hweight

/--
[ons_KWmatPhase_det_eq_walk_exp_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma ons_KWmatPhase_det_eq_walk_exp_critical_eq
  {L : Nat}
  [NeZero L]
  {q : Real}
  {a b : Fin 2}
-- given
  (hq0 : 0 <= q)
  (hq : q < ons_signedLoopCriticalWeight) :
-- imply
  (1 - ons_KWmatPhase L (q : Complex) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det = Complex.exp (- ∑' n : Nat, (∑ v : Fin (n + 1) -> ons_Dart L, ∏ k : Fin (n + 1), ons_KWmatPhase L (q : Complex) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (v k) (v (k + 1))) / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_det_eq_walk_exp_critical L q hq0 hq a b

/--
[ons_KWmatPhase_tanh_det_eq_walk_exp_before_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectralCritical.lean)
-/
@[path]
private lemma ons_KWmatPhase_tanh_det_eq_walk_exp_before_betaC_eq
  {L : Nat}
  [NeZero L]
  {beta : Real}
  {a b : Fin 2}
-- given
  (hbeta0 : 0 <= beta)
  (hbetaC : beta < ons_betaC) :
-- imply
  (1 - ons_KWmatPhase L (Real.tanh beta : Complex) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det = Complex.exp (- ∑' n : Nat, (∑ v : Fin (n + 1) -> ons_Dart L, ∏ k : Fin (n + 1), ons_KWmatPhase L (Real.tanh beta : Complex) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (v k) (v (k + 1))) / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_tanh_det_eq_walk_exp_before_betaC L beta hbeta0 hbetaC a b


-- created on 2026-10-23
