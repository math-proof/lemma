import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedCancellation
open StatMech StatMech.Onsager


/--
[ons_KWmatWeightedPhase_mask_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedCancellation.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_mask_surgery_sign_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden)
  (hd : d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e)) :
-- imply
  ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) (ons_surgery e (ons_dartRev L) d) = -ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) d := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_mask_surgery_sign weight omega homega a b forbidden hforbidden e d hd

/--
[ons_KWmatWeightedPhase_mask_lemma5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedCancellation.lean)
-/
@[path]
private lemma ons_KWmatWeightedPhase_mask_lemma5_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ∑ d ∈ ons_loopSetBoth (n := n) e (ons_dartRev L e), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) d = 0 := by
-- proof
  apply StatMech.Onsager.ons_KWmatWeightedPhase_mask_lemma5 weight omega homega a b forbidden hforbidden e

/--
[ons_loopSum_KWmatWeightedPhase_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedCancellation.lean)
-/
@[path]
private lemma ons_loopSum_KWmatWeightedPhase_both_zero_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  (∑ d ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e)), ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_loopSum_KWmatWeightedPhase_both_zero n weight omega homega a b e

/--
[ons_loopSum_KWmatWeightedPhase_mask_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedCancellation.lean)
-/
@[path]
private lemma ons_loopSum_KWmatWeightedPhase_mask_both_zero_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ d ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter (fun d => (∃ i, d i = e) ∧ (∃ j, d j = ons_dartRev L e)), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_loopSum_KWmatWeightedPhase_mask_both_zero n weight omega homega a b forbidden hforbidden e

/--
[ons_loopWeight_KWmatWeightedPhase_mask_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedCancellation.lean)
-/
@[path]
private lemma ons_loopWeight_KWmatWeightedPhase_mask_loopRev_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {d : Fin n → ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) (ons_loopRev L d) = ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_KWmatWeightedPhase_mask_loopRev weight omega homega a b forbidden hforbidden d

/--
[ons_loopSum_KWmatWeightedPhase_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedCancellation.lean)
-/
@[path]
private lemma ons_loopSum_KWmatWeightedPhase_symm_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I) :
-- imply
  (∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L => (∃ i, d i = e) ∧ ¬ ∃ j, d j = ons_dartRev L e)), ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d) = ∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L => (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e)), ons_loopWeight (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b)) d := by
-- proof
  apply StatMech.Onsager.ons_loopSum_KWmatWeightedPhase_symm weight omega homega a b e

/--
[ons_loopSum_KWmatWeightedPhase_mask_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeightedCancellation.lean)
-/
@[path]
private lemma ons_loopSum_KWmatWeightedPhase_mask_symm_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {omega : ℂ}
  {a b : Fin 2}
  {forbidden : Finset (ons_Dart L)}
  {e : ons_Dart L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hforbidden : ∀ d, ons_dartRev L d ∈ forbidden ↔ d ∈ forbidden) :
-- imply
  (∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L => (∃ i, d i = e) ∧ ¬ ∃ j, d j = ons_dartRev L e)), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) d) = ∑ d ∈ (Finset.univ.filter (fun d : Fin n → ons_Dart L => (∃ i, d i = ons_dartRev L e) ∧ ¬ ∃ j, d j = e)), ons_loopWeight (ons_maskMatrix forbidden (ons_KWmatWeightedPhase L weight omega (ons_spinPhase L a) (ons_spinPhase L b))) d := by
-- proof
  apply StatMech.Onsager.ons_loopSum_KWmatWeightedPhase_mask_symm weight omega homega a b forbidden hforbidden e


-- created on 2026-10-23
