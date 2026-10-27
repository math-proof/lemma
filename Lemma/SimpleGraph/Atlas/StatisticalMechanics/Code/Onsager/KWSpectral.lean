import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
open StatMech StatMech.Onsager


/--
[norm_ons_spinPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma norm_ons_spinPhase_eq
  {L : ℕ}
  {a : Fin 2} :
-- imply
  ‖ons_spinPhase L a‖ = 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_spinPhase L a

/--
[norm_ons_turnRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma norm_ons_turnRoot_eq :
-- imply
  ‖ons_turnRoot‖ = 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_turnRoot

/--
[norm_ons_turnW_turnRoot_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma norm_ons_turnW_turnRoot_le_one_eq
  {mu nu : Fin 4} :
-- imply
  ‖ons_turnW ons_turnRoot mu nu‖ ≤ 1 := by
-- proof
  apply StatMech.Onsager.norm_ons_turnW_turnRoot_le_one mu nu

/--
[nnnorm_ons_KWmatPhase_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma nnnorm_ons_KWmatPhase_le_eq
  {L : ℕ}
  {x : ℝ}
  {a b : Fin 2}
  {d2 d1 : ons_Dart L} :
-- imply
  ‖ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖₊ ≤ ‖(x : ℂ)‖₊ := by
-- proof
  apply StatMech.Onsager.nnnorm_ons_KWmatPhase_le L x a b d2 d1

/--
[norm_ons_KWmatPhase_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma norm_ons_KWmatPhase_le_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2} :
-- imply
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) := Matrix.linftyOpNormedRing ‖ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)‖ ≤ Fintype.card (ons_Dart L) * ‖x‖ := by
-- proof
  apply StatMech.Onsager.norm_ons_KWmatPhase_le L x a b

/--
[ons_KWmatPhase_spectral_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma ons_KWmatPhase_spectral_lt_one_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2}
-- given
  (hx : Fintype.card (ons_Dart L) * ‖x‖ < 1) :
-- imply
  ∀ alpha ∈ (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_spectral_lt_one L x a b hx

/--
[ons_KWconvergenceRadius_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma ons_KWconvergenceRadius_pos_eq
  {L : ℕ}
  [NeZero L] :
-- imply
  0 < ons_KWconvergenceRadius L := by
-- proof
  apply StatMech.Onsager.ons_KWconvergenceRadius_pos L

/--
[ons_KWmatPhase_spectral_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma ons_KWmatPhase_spectral_small_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_KWconvergenceRadius L)) :
-- imply
  ∀ alpha ∈ (ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots, ‖alpha‖ < 1 := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_spectral_small L hx a b

/--
[ons_KWmatPhase_det_eq_walk_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean)
-/
@[path]
private lemma ons_KWmatPhase_det_eq_walk_exp_eq
  {L : ℕ}
  [NeZero L]
  {x : ℝ}
  {a b : Fin 2}
-- given
  (hx : x ∈ Set.Ioo (0 : ℝ) (ons_KWconvergenceRadius L)) :
-- imply
  (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det = Complex.exp (- ∑' n : ℕ, (∑ v : Fin (n + 1) → ons_Dart L, ∏ k : Fin (n + 1), ons_KWmatPhase L (x : ℂ) ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b) (v k) (v (k + 1))) / (n + 1)) := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_det_eq_walk_exp L hx a b


-- created on 2026-10-23
