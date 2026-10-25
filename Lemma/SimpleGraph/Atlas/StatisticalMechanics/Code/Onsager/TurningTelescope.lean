import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
open StatMech StatMech.Onsager


/--
[ons_dirStep_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_dirStep_opposite_eq
  {L : ℕ}
  {μ : Fin 4}
  {p : ZMod L × ZMod L} :
-- imply
  ons_dirStep L (μ + 2) (ons_dirStep L μ p) = p := by
-- proof
  apply StatMech.Onsager.ons_dirStep_opposite L μ p

/--
[ons_dartRev_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_dartRev_involutive_eq
  {L : ℕ} :
-- imply
  Function.Involutive (ons_dartRev L) := by
-- proof
  apply StatMech.Onsager.ons_dartRev_involutive L

/--
[ons_dartRev_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_dartRev_ne_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  ons_dartRev L d ≠ d := by
-- proof
  apply StatMech.Onsager.ons_dartRev_ne L d

/--
[ons_turnZ_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_turnZ_telescope_eq
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4} :
-- imply
  (∑ k : Fin n, ((d k.succ : ZMod 4) - (d k.castSucc : ZMod 4))) = (d (Fin.last n) : ZMod 4) - (d 0 : ZMod 4) := by
-- proof
  apply StatMech.Onsager.ons_turnZ_telescope n d

/--
[ons_turnW_eq_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_turnW_eq_zpow_eq
  {ω : ℂ}
  {μ ν : Fin 4}
-- given
  (h : ν ≠ μ + 2) :
-- imply
  ons_turnW ω μ ν = ω ^ (ons_turnPow μ ν) := by
-- proof
  apply StatMech.Onsager.ons_turnW_eq_zpow ω μ ν h

/--
[ons_prod_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_prod_zpow_eq
  {ω : ℂ}
  {s : Finset ι}
  {f : ι → ℤ}
-- given
  (hω : ω ≠ 0) :
-- imply
  ∏ i ∈ s, ω ^ (f i) = ω ^ (∑ i ∈ s, f i) := by
-- proof
  apply StatMech.Onsager.ons_prod_zpow ω hω s f

/--
[ons_turnPow_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_turnPow_cast_eq
  {μ ν : Fin 4}
-- given
  (h : ν ≠ μ + 2) :
-- imply
  ((ons_turnPow μ ν : ℤ) : ZMod 4) = ons_turnZ μ ν := by
-- proof
  apply StatMech.Onsager.ons_turnPow_cast μ ν h

/--
[ons_walk_prod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_walk_prod_eq_eq
  {ω : ℂ}
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
-- given
  (hω : ω ≠ 0)
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
-- imply
  ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = ω ^ (∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ)) := by
-- proof
  apply StatMech.Onsager.ons_walk_prod_eq ω hω n d hnu

/--
[ons_walk_turnPow_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_walk_turnPow_mod_eq
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
-- given
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2) :
-- imply
  ((∑ k : Fin n, ons_turnPow (d k.castSucc) (d k.succ) : ℤ) : ZMod 4) = (d (Fin.last n) : ZMod 4) - (d 0 : ZMod 4) := by
-- proof
  apply StatMech.Onsager.ons_walk_turnPow_mod n d hnu

/--
[ons_omega_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_omega_pow_four_eq
  {ω : ℂ}
-- given
  (h : ω ^ 2 = Complex.I) :
-- imply
  ω ^ 4 = -1 := by
-- proof
  apply StatMech.Onsager.ons_omega_pow_four ω h

/--
[ons_walk_prod_antipodal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TurningTelescope.lean)
-/
@[path]
private lemma ons_walk_prod_antipodal_eq
  {ω : ℂ}
  {n : ℕ}
  {d : Fin (n + 1) → Fin 4}
-- given
  (hω : ω ≠ 0)
  (hI : ω ^ 2 = Complex.I)
  (hnu : ∀ k : Fin n, d k.succ ≠ d k.castSucc + 2)
  (hend : d (Fin.last n) = d 0 + 2) :
-- imply
  ∃ m : ℤ, ∏ k : Fin n, ons_turnW ω (d k.castSucc) (d k.succ) = (-1) ^ m * Complex.I := by
-- proof
  apply StatMech.Onsager.ons_walk_prod_antipodal ω hω hI n d hnu hend


-- created on 2026-10-23
