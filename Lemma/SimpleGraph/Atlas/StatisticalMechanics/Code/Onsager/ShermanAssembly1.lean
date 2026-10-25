import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanAssembly1
open StatMech StatMech.Onsager


/--
[ons_sum_split_by_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly1.lean)
-/
@[path]
private lemma ons_sum_split_by_two_eq
  [Fintype β]
  [DecidablePred P]
  [DecidablePred Q]
  {f : β → ℂ}
-- given
  (P Q : β → Prop) :
-- imply
  (∑ v ∈ (Finset.univ : Finset β), f v) = (∑ v ∈ Finset.univ.filter (fun v => ¬ P v ∧ ¬ Q v), f v) + (∑ v ∈ Finset.univ.filter (fun v => P v ∧ ¬ Q v), f v) + (∑ v ∈ Finset.univ.filter (fun v => ¬ P v ∧ Q v), f v) + (∑ v ∈ Finset.univ.filter (fun v => P v ∧ Q v), f v) := by
-- proof
  apply StatMech.Onsager.ons_sum_split_by_two P Q f

/--
[ons_KW_loopSum_split_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly1.lean)
-/
@[path]
private lemma ons_KW_loopSum_split_four_eq
  {L : ℕ}
  [NeZero L]
  {n : ℕ}
  {x ω : ℂ}
  {e : ons_Dart L} :
-- imply
  (∑ v ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) = (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L => ¬ (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) + (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L => (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) + (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L => ¬ (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) + (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L => (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) := by
-- proof
  apply StatMech.Onsager.ons_KW_loopSum_split_four n x ω e

/--
[ons_loopSum_both_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly1.lean)
-/
@[path]
private lemma ons_loopSum_both_zero_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {x ω : ℂ}
  {e : ons_Dart L}
-- given
  (hω : ω ^ 2 = Complex.I) :
-- imply
  (∑ v ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)).filter (fun v => (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) = 0 := by
-- proof
  apply StatMech.Onsager.ons_loopSum_both_zero n x ω hω e

/--
[ons_KW_loopSum_no_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanAssembly1.lean)
-/
@[path]
private lemma ons_KW_loopSum_no_both_eq
  {L : ℕ}
  [NeZero L]
  [Fact (2 < L)]
  {n : ℕ}
  {x ω : ℂ}
  {e : ons_Dart L}
-- given
  (hω : ω ^ 2 = Complex.I) :
-- imply
  (∑ v ∈ (Finset.univ : Finset (Fin (n + 1) → ons_Dart L)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) = (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L => (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) + (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L => ¬ (∃ i, v i = e) ∧ (∃ j, v j = ons_dartRev L e)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) + (∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → ons_Dart L => ¬ (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)), ∏ k : Fin (n + 1), ons_KWmat L x ω (v k) (v (k + 1))) := by
-- proof
  apply StatMech.Onsager.ons_KW_loopSum_no_both n x ω hω e


-- created on 2026-10-23
