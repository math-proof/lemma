import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLemma5
open StatMech StatMech.Onsager


/--
[ons_dirPhase_spin_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_dirPhase_spin_opposite_eq
  {L : ℕ}
  {a b : Fin 2}
  {mu : Fin 4} :
-- imply
  ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (mu + 2) = (ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) mu)⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_dirPhase_spin_opposite L a b mu

/--
[ons_spinPhase_loopFactor_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_spinPhase_loopFactor_sq_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  (∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (d k).2) ^ 2 = 1 := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_loopFactor_sq a b d hvalid

/--
[ons_spinPhase_surgeryFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_spinPhase_surgeryFactor_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {a b : Fin 2}
  {e : ons_Dart L}
  {d : Fin n → ons_Dart L}
-- given
  (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e))
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  (∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (ons_surgery e (ons_dartRev L) d k).2) = ∏ k, ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) (d k).2 := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_surgeryFactor a b e d hd hvalid

/--
[ons_KWmatPhase_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_KWmatPhase_surgery_sign_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) (ons_surgery e (ons_dartRev L) d) = -ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_surgery_sign x omega homega a b e d hd

/--
[ons_KWmatPhase_mask_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_KWmatPhase_mask_surgery_sign_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
  (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
-- imply
  ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) (ons_surgery e (ons_dartRev L) d) = -ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) d := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_mask_surgery_sign x omega homega a b forbidden hforbidden e d hd

/--
[ons_KWmatPhase_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_KWmatPhase_lemma5_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  ∑ d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e), ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d = 0 := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_lemma5 x omega homega a b e

/--
[ons_KWmatPhase_mask_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_KWmatPhase_mask_lemma5_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {x omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ∑ d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) d = 0 := by
-- proof
  apply StatMech.Onsager.ons_KWmatPhase_mask_lemma5 x omega homega a b forbidden hforbidden e

/--
[ons_loopSum_spinPhase_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_loopSum_spinPhase_both_zero_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {x omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  (∑ d ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e)), ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_loopSum_spinPhase_both_zero n x omega homega a b e

/--
[ons_loopSum_spinPhase_mask_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWPhaseLemma5.lean)
-/
@[path]
private lemma ons_loopSum_spinPhase_mask_both_zero_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {x omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ d ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e)), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b))) d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_loopSum_spinPhase_mask_both_zero n x omega homega a b forbidden hforbidden e


-- created on 2026-10-23
