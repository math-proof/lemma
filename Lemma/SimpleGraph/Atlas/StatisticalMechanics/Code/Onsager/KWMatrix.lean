import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWMatrix
open StatMech StatMech.Onsager


/--
[ons_turnW_straight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMatrix.lean)
-/
@[path]
private lemma ons_turnW_straight_eq
  {ω : ℂ}
  {μ : Fin 4} :
-- imply
  ons_turnW ω μ μ = 1 := by
-- proof
  apply StatMech.Onsager.ons_turnW_straight ω μ

/--
[ons_turnW_uturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMatrix.lean)
-/
@[path]
private lemma ons_turnW_uturn_eq
  {ω : ℂ}
  {μ : Fin 4} :
-- imply
  ons_turnW ω μ (μ + 2) = 0 := by
-- proof
  apply StatMech.Onsager.ons_turnW_uturn ω μ

/--
[ons_dirStep_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMatrix.lean)
-/
@[path]
private lemma ons_dirStep_shift_eq
  {L : ℕ}
  {μ : Fin 4}
  {t s : ZMod L × ZMod L} :
-- imply
  ons_dirStep L μ (s.1 + t.1, s.2 + t.2) = ((ons_dirStep L μ s).1 + t.1, (ons_dirStep L μ s).2 + t.2) := by
-- proof
  apply StatMech.Onsager.ons_dirStep_shift L μ t s

/--
[ons_KWmat_translation_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWMatrix.lean)
-/
@[path]
private lemma ons_KWmat_translation_invariant_eq
  {L : ℕ}
  {x ω : ℂ}
  {t : ZMod L × ZMod L}
  {d₁ d₂ : ons_Dart L} :
-- imply
  ons_KWmat L x ω (ons_shiftDart L t d₂) (ons_shiftDart L t d₁) = ons_KWmat L x ω d₂ d₁ := by
-- proof
  apply StatMech.Onsager.ons_KWmat_translation_invariant L x ω t d₁ d₂


-- created on 2026-10-23
