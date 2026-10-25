import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Matching.GaleShapley.Part7
open MathlibExt.Combinatorics.Matching.GaleShapley
open StrictTotalOrder


namespace MathlibExt.Combinatorics.Matching.GaleShapley.StrictTotalOrder

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
lemma ext
  {T T' : StrictTotalOrder α}
-- given
  (h : T.lt = T'.lt) :
-- imply
  T = T' :=
-- proof
  MathlibExt.Order.StrictTotalOrder.ext h

end MathlibExt.Combinatorics.Matching.GaleShapley.StrictTotalOrder

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[isBlockingPair_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
lemma isBlockingPair_iff
  {mp : MPrefs M W}
  {wp : WPrefs M W}
  {μ : PerfectMatching M W}
  {m : M}
  {w : W} :
-- imply
  IsBlockingPair mp wp μ m w ↔ (mp m).lt w (μ m) ∧ (wp w).lt m (μ.symm w) :=
-- proof
  Iff.rfl

end MathlibExt.Combinatorics.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[isStable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
lemma isStable_iff
  {mp : MPrefs M W}
  {wp : WPrefs M W}
  {μ : PerfectMatching M W} :
-- imply
  IsStable mp wp μ ↔ ∀ m w, ¬ IsBlockingPair mp wp μ m w :=
-- proof
  Iff.rfl

end MathlibExt.Combinatorics.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[dostep_prop](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma dostep_prop {M W : Type*} [DecidableEq M] [DecidableEq W]
  (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W)
  (m' : M) :
  (dostep mp wp s m0 w0).prop m' =
    (if m' = m0 then insert w0 (s.prop m0) else s.prop m') :=
  rfl

end MathlibExt.Combinatorics.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[dostep_hold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma dostep_hold {M W : Type*} [DecidableEq M] [DecidableEq W]
  (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W)
  (w' : W) :
  (dostep mp wp s m0 w0).hold w' =
    (if w' = w0 then some (womanChoice (wp w0) (s.hold w0) m0) else s.hold w') :=
  rfl

end MathlibExt.Combinatorics.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[dostep_measure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma dostep_measure {M W : Type*} [Fintype M] [DecidableEq M] [DecidableEq W]
  (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W)
  (hnew : w0 ∉ s.prop m0) :
  DAMeasure (dostep mp wp s m0 w0) = DAMeasure s + 1 := by
  change (∑ m ∈ Finset.univ, ((dostep mp wp s m0 w0).prop m).card) =
    (∑ m ∈ Finset.univ, (s.prop m).card) + 1
  have hp : ∀ m', (dostep mp wp s m0 w0).prop m' =
    (if m' = m0 then insert w0 (s.prop m0) else s.prop m') :=
    fun m' => dostep_prop mp wp s m0 w0 m'
  have e1 : ((dostep mp wp s m0 w0).prop m0).card +
    ∑ x ∈ Finset.univ.erase m0, ((dostep mp wp s m0 w0).prop x).card =
    ∑ x ∈ Finset.univ, ((dostep mp wp s m0 w0).prop x).card :=
    Finset.add_sum_erase Finset.univ
      (fun x => ((dostep mp wp s m0 w0).prop x).card) (Finset.mem_univ m0)
  have e2 : (s.prop m0).card + ∑ x ∈ Finset.univ.erase m0, (s.prop x).card =
    ∑ x ∈ Finset.univ, (s.prop x).card :=
    Finset.add_sum_erase Finset.univ
      (fun x => (s.prop x).card) (Finset.mem_univ m0)
  have e3 : (∑ x ∈ Finset.univ.erase m0, ((dostep mp wp s m0 w0).prop x).card) =
    ∑ x ∈ Finset.univ.erase m0, (s.prop x).card := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hp, ite_eq_right (Finset.ne_of_mem_erase hx)]
  have e4 : ((dostep mp wp s m0 w0).prop m0).card = (s.prop m0).card + 1 := by
    rw [hp, ite_eq_left rfl, Finset.card_insert_of_notMem hnew]
  omega

end MathlibExt.Combinatorics.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[DAMeasure_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma DAMeasure_le {M W : Type*} [Fintype M] [Fintype W]
  (s : DAState M W) : DAMeasure s ≤ Fintype.card M * Fintype.card W := by
  unfold DAMeasure
  calc ∑ m ∈ Finset.univ, (s.prop m).card
    ≤ Finset.univ.card • Fintype.card W :=
      Finset.sum_le_card_nsmul _ _ _ (fun m _ => Finset.card_le_univ _)
    _ = Fintype.card M * Fintype.card W := by
      rw [Finset.card_univ, smul_eq_mul]

end MathlibExt.Combinatorics.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[dainit_inv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma dainit_inv {M W : Type*}
  (mp : MPrefs M W) (wp : WPrefs M W) : DAInv mp wp dainit := by
  refine ⟨fun w m' hw => ?_, fun w m hw => ?_, fun w m hw => ?_,
    fun m w₁ w₂ h₁ h₂ => ?_, fun m w w' hw => ?_⟩
  · simp [dainit] at hw
  · simp [dainit] at hw
  · simp [dainit] at hw
  · simp [dainit] at h₁
  · simp [dainit] at hw

end MathlibExt.Combinatorics.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[dainit_measure](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma dainit_measure {M W : Type*} [Fintype M] :
  DAMeasure (dainit : DAState M W) = 0 := by
  simp [DAMeasure, dainit]

end MathlibExt.Combinatorics.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

/--
[gale_shapley_exists_stable_matching](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
lemma gale_shapley_exists_stable_matching
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  {mp : MPrefs M W}
  {wp : WPrefs M W}
-- given
  (hCard : Fintype.card M = Fintype.card W) :
-- imply
  ∃ μ : PerfectMatching M W, IsStable mp wp μ :=
-- proof
  gale_shapley_exists_stable_matching_general hCard mp wp

end MathlibExt.Combinatorics.Matching.GaleShapley

/--
[gale_shapley_exists_stable_matching_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean)
-/
@[path]
private lemma gale_shapley_exists_stable_matching_general_eq
  [Fintype M] [Fintype W]
  {mp : MPrefs M W}
  {wp : WPrefs M W}
-- given
  (hCard : Fintype.card M = Fintype.card W) :
-- imply
  ∃ μ : PerfectMatching M W, IsStable mp wp μ := by
-- proof
  apply MathlibExt.Combinatorics.Matching.GaleShapley.gale_shapley_exists_stable_matching_general hCard mp wp


-- created on 2026-10-20
-- updated on 2026-10-23
