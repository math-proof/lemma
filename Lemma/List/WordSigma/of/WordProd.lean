import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.List.IsReducedDrop.of.IsReduced
import Lemma.Nat.EqBilinInversions
import Lemma.List.Any_And_IsReduced_EraseIdx.of.LtLengthMulWordProdSimple_Length_WordProd.IsReduced.SignChangeExchangeHyp
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.SimpleReflectionInversions
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.StrongExchangeBridge
open CoxeterGroup CoxeterSignChangeExchangeFinal


namespace DescentInversionBridge

/--
[wordSigma_eq_of_wordProd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma wordSigma_eq_of_wordProd_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word₁ word₂ : List B}
  {v : B → ℝ}
-- given
  (h : cs.wordProd word₁ = cs.wordProd word₂) :
-- imply
  wordSigma M word₁ v = wordSigma M word₂ v := by
-- proof
  have h1 := coxeterRepresentation_wordProd_apply M cs word₁ v
  have h2 := coxeterRepresentation_wordProd_apply M cs word₂ v
  rw [h] at h1
  rw [← h1, ← h2]

end DescentInversionBridge

namespace DescentInversionBridge

/--
[descent_implies_isNegative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma descent_implies_isNegative
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {i : B}
-- given
  (hred : cs.IsReduced word)
  (hdesc : cs.IsRightDescent (cs.wordProd word) i) :
-- imply
  IsNegative (wordSigma M word (e i)) := by
-- proof
  have hlt : cs.length (cs.wordProd word * cs.simple i) <
    cs.length (cs.wordProd word) := by
    rw [CoxeterSystem.isRightDescent_iff] at hdesc; omega
  exact neg_of_descent M cs word i hred hlt

end DescentInversionBridge

namespace DescentInversionBridge

/--
[isNegative_implies_descent'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma isNegative_implies_descent'
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {i : B}
-- given
  (hred : cs.IsReduced word)
  (hneg : IsNegative (wordSigma M word (e i))) :
-- imply
  cs.IsRightDescent (cs.wordProd word) i := by
-- proof
  have hlt := isNegative_implies_descent M cs word i hred hneg
  rw [CoxeterSystem.isRightDescent_iff]
  obtain h | h <;> omega := cs.length_mul_simple (cs.wordProd word) i

end DescentInversionBridge

namespace DescentInversionBridge

/--
[descent_iff_isNegative](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma descent_iff_isNegative
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {i : B}
-- given
  (hred : cs.IsReduced word) :
-- imply
  cs.IsRightDescent (cs.wordProd word) i ↔ IsNegative (wordSigma M word (e i)) :=
-- proof
  ⟨descent_implies_isNegative M cs word i hred,
    isNegative_implies_descent' M cs word i hred⟩

end DescentInversionBridge

namespace DescentInversionBridge

/--
[ascent_implies_isPositive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma ascent_implies_isPositive
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {i : B}
-- given
  (hred : cs.IsReduced word)
  (hasc : ¬cs.IsRightDescent (cs.wordProd word) i) :
-- imply
  IsPositive (wordSigma M word (e i)) := by
-- proof
  have hgt : cs.length (cs.wordProd word * cs.simple i) >
    cs.length (cs.wordProd word) := by
    rw [CoxeterSystem.not_isRightDescent_iff] at hasc
    omega
  exact pos_of_ascent M cs word i hred hgt

end DescentInversionBridge

namespace DescentInversionBridge

/--
[isPositive_implies_ascent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma isPositive_implies_ascent
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {i : B}
-- given
  (hred : cs.IsReduced word)
  (hpos : IsPositive (wordSigma M word (e i))) :
-- imply
  ¬cs.IsRightDescent (cs.wordProd word) i := by
-- proof
  intro hdesc
  have hneg := descent_implies_isNegative M cs word i hred hdesc
  have hzero := isPositive_isNegative_eq_zero hpos hneg
  have hform := wordSigma_preserves_form M word (e i) (e i)
  rw [hzero] at hform
  simp [bilinForm_zero_left] at hform
  linarith [show bilinForm M (e i) (e i) = 1 from by rw [bilinForm_e_e, formVal_diag]]

end DescentInversionBridge

namespace DescentInversionBridge

/--
[ascent_iff_isPositive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma ascent_iff_isPositive
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {i : B}
-- given
  (hred : cs.IsReduced word) :
-- imply
  ¬cs.IsRightDescent (cs.wordProd word) i ↔ IsPositive (wordSigma M word (e i)) :=
-- proof
  ⟨ascent_implies_isPositive M cs word i hred,
    isPositive_implies_ascent M cs word i hred⟩

end DescentInversionBridge

namespace DescentInversionBridge

/--
[wordSigma_append_isNegative_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma wordSigma_append_isNegative_toggle
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B} :
-- imply
  IsNegative (wordSigma M (word ++ [s]) (e s)) ↔ IsPositive (wordSigma M word (e s)) := by
-- proof
  have hflip := wordSigma_append_s_neg M word s
  constructor
  · intro hneg t
    have := hneg t
    rw [hflip] at this
    simp at this
    linarith
  · intro hpos t
    rw [hflip]
    simp
    exact hpos t

end DescentInversionBridge

namespace DescentInversionBridge

/--
[wordSigma_append_isPositive_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma wordSigma_append_isPositive_toggle
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B} :
-- imply
  IsPositive (wordSigma M (word ++ [s]) (e s)) ↔ IsNegative (wordSigma M word (e s)) := by
-- proof
  have hflip := wordSigma_append_s_neg M word s
  constructor
  · intro hpos t
    have := hpos t
    rw [hflip] at this
    simp at this
    linarith
  · intro hneg t
    rw [hflip]
    simp
    have := hneg t
    linarith

end DescentInversionBridge

namespace DescentInversionBridge

/--
[descent_toggle_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma descent_toggle_append
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (hred_word : cs.IsReduced word)
  (hred_app : cs.IsReduced (word ++ [s])) :
-- imply
  cs.IsRightDescent (cs.wordProd (word ++ [s])) s ↔ ¬cs.IsRightDescent (cs.wordProd word) s := by
-- proof
  rw [descent_iff_isNegative M cs (word ++ [s]) s hred_app,
    wordSigma_append_isNegative_toggle,
    ← ascent_iff_isPositive M cs word s hred_word]

end DescentInversionBridge

namespace DescentInversionBridge

/--
[exists_reduced_word_ending_in_descent'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma exists_reduced_word_ending_in_descent'
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w : W}
  {s : B}
-- given
  (hdesc : cs.IsRightDescent w s) :
-- imply
  ∃ prefix_word, cs.IsReduced (prefix_word ++ [s]) ∧ cs.wordProd (prefix_word ++ [s]) = w := by
-- proof
  have hlt : cs.length (w * cs.simple s) < cs.length w := by
    rw [CoxeterSystem.isRightDescent_iff] at hdesc; omega
  exact StrongExchangeBridge.exists_reduced_word_ending_in_descent w s hlt

end DescentInversionBridge

namespace DescentInversionBridge

/--
[descent_iff_isNegative_any_word](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma descent_iff_isNegative_any_word
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {w : W}
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced word)
  (hprod : cs.wordProd word = w) :
-- imply
  cs.IsRightDescent w s ↔ IsNegative (wordSigma M word (e s)) := by
-- proof
  rw [← hprod]
  exact descent_iff_isNegative M cs word s hred

end DescentInversionBridge

namespace DescentInversionBridge

/--
[mem_bilinInversions_implies_isRightDescent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma mem_bilinInversions_implies_isRightDescent
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced word)
  (hmem : s ∈ bilinInversions M word) :
-- imply
  cs.IsRightDescent (cs.wordProd word) s := by
-- proof
  rw [CoxeterGroup.mem_bilinInversions_iff] at hmem
  by_contra hasc
  have hasc' : ¬cs.IsRightDescent (cs.wordProd word) s := hasc
  have hpos := ascent_implies_isPositive M cs word s hred hasc'
  linarith [hpos s]

end DescentInversionBridge

namespace DescentInversionBridge

/--
[wordSigma_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma wordSigma_ne_zero
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B} :
-- imply
  wordSigma M word (e s) ≠ 0 := by
-- proof
  intro h
  have hform := wordSigma_preserves_form M word (e s) (e s)
  rw [h] at hform
  simp [bilinForm_zero_left] at hform
  linarith [show bilinForm M (e s) (e s) = 1 from by rw [bilinForm_e_e, formVal_diag]]

end DescentInversionBridge

namespace DescentInversionBridge

/--
[isNegative_exists_neg_component](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma isNegative_exists_neg_component
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B}
-- given
  (hneg : IsNegative (wordSigma M word (e s))) :
-- imply
  ∃ t, wordSigma M word (e s) t < 0 := by
-- proof
  by_contra h
  push_neg at h
  have hzero : wordSigma M word (e s) = 0 := by
    ext t; simp only [Pi.zero_apply]; linarith [h t, hneg t]
  exact wordSigma_ne_zero M word s hzero

end DescentInversionBridge

namespace DescentInversionBridge

/--
[descent_exists_neg_component](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma descent_exists_neg_component
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced word)
  (hdesc : cs.IsRightDescent (cs.wordProd word) s) :
-- imply
  ∃ t, wordSigma M word (e s) t < 0 :=
-- proof
  isNegative_exists_neg_component M word s
    (descent_implies_isNegative M cs word s hred hdesc)

end DescentInversionBridge

namespace DescentInversionBridge

/--
[ascent_exists_pos_component](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma ascent_exists_pos_component
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced word)
  (hasc : ¬cs.IsRightDescent (cs.wordProd word) s) :
-- imply
  ∃ t, wordSigma M word (e s) t > 0 := by
-- proof
  have hpos := ascent_implies_isPositive M cs word s hred hasc
  by_contra h
  push_neg at h
  have hzero : wordSigma M word (e s) = 0 := by
    ext t; simp only [Pi.zero_apply]; linarith [h t, hpos t]
  exact wordSigma_ne_zero M word s hzero

end DescentInversionBridge

namespace DescentInversionBridge

/--
[bilinInversions_eq_of_wordProd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma bilinInversions_eq_of_wordProd_eq
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word₁ word₂ : List B}
-- given
  (h : cs.wordProd word₁ = cs.wordProd word₂) :
-- imply
  bilinInversions M word₁ = bilinInversions M word₂ := by
-- proof
  ext s
  simp only [CoxeterGroup.mem_bilinInversions_iff]
  have := wordSigma_eq_of_wordProd_eq M cs word₁ word₂ h (e s)
  constructor
  · intro h1; rw [← this]; exact h1
  · intro h2; rw [this]; exact h2

end DescentInversionBridge

namespace DescentInversionBridge

/--
[bilinInversions_self_toggle_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma bilinInversions_self_toggle_of_ne_zero
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {word : List B}
  {s : B}
-- given
  (hne : wordSigma M word (e s) s ≠ 0) :
-- imply
  s ∈ bilinInversions M (word ++ [s]) ↔ s ∉ bilinInversions M word :=
-- proof
  bilinInversions_append_toggle M word s hne

end DescentInversionBridge

namespace DescentInversionBridge

/--
[bilinInversions_nil'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma bilinInversions_nil'
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  bilinInversions M ([] : List B) = ∅ :=
-- proof
  bilinInversions_nil M

end DescentInversionBridge

namespace DescentInversionBridge

/--
[bilinInversions_singleton'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma bilinInversions_singleton'
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B} :
-- imply
  bilinInversions M [s] = {s} :=
-- proof
  bilinInversions_singleton M s

end DescentInversionBridge

namespace DescentInversionBridge

/--
[isRightDescent_of_reduced_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma isRightDescent_of_reduced_append
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced (word ++ [s])) :
-- imply
  cs.IsRightDescent (cs.wordProd (word ++ [s])) s := by
-- proof
  rw [CoxeterSystem.isRightDescent_iff]
  have hlen : cs.length (cs.wordProd (word ++ [s])) = word.length + 1 := by
    rw [CoxeterSystem.IsReduced] at hred
    rw [hred, List.length_append, List.length_singleton]
  have hle : cs.length (cs.wordProd word) ≤ word.length := cs.length_wordProd_le word
  rw [cs.wordProd_append, cs.wordProd_singleton, mul_assoc,
    cs.simple_mul_simple_self, mul_one]
  rw [cs.wordProd_append, cs.wordProd_singleton] at hlen
  obtain h | h <;> omega := cs.length_mul_simple (cs.wordProd word) s

end DescentInversionBridge

namespace DescentInversionBridge

/--
[not_isRightDescent_of_reduced_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DescentInversionBridge.lean)
-/
@[path]
lemma not_isRightDescent_of_reduced_prefix
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {s : B}
-- given
  (hred : cs.IsReduced (word ++ [s])) :
-- imply
  ¬cs.IsRightDescent (cs.wordProd word) s := by
-- proof
  rw [CoxeterSystem.not_isRightDescent_iff]
  have hred_word : cs.IsReduced word := by
    have := hred.take word.length
    rwa [List.take_left] at this
  have hlen_word : cs.length (cs.wordProd word) = word.length := by
    rw [CoxeterSystem.IsReduced] at hred_word; exact hred_word
  have hlen_app : cs.length (cs.wordProd (word ++ [s])) = word.length + 1 := by
    rw [CoxeterSystem.IsReduced] at hred
    rw [hred, List.length_append, List.length_singleton]
  rw [cs.wordProd_append, cs.wordProd_singleton] at hlen_app
  omega

end DescentInversionBridge


-- created on 2026-10-23
