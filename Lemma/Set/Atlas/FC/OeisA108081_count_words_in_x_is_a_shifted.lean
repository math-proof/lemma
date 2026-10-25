import Mathlib
import sympy.Basic
import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part13
open OeisA108081
open Nat
open PowerSeries


namespace OeisA108081

/--
[mem_l_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma mem_l_iff
  {z : ℤ}
  {w : Word} :
-- imply
  z ∈ l w ↔ z + 1 ∈ w := by
-- proof
  simp [l]
  constructor <;> intro h
  · obtain ⟨x, hx, rfl⟩ := h
    simpa using hx
  · exact ⟨z + 1, by simpa using h, by omega⟩

end OeisA108081

namespace OeisA108081

/--
[mem_r_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma mem_r_iff
  {z : ℤ}
  {w : Word} :
-- imply
  z ∈ r w ↔ z - 1 ∈ w := by
-- proof
  simp [r]
  constructor <;> intro h
  · obtain ⟨x, hx, rfl⟩ := h
    simpa using hx
  · exact ⟨z - 1, by simpa using h, by omega⟩

end OeisA108081

namespace OeisA108081

/--
[even_pred_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma even_pred_iff
  {z : ℤ} :
-- imply
  Even (z - 1) ↔ ¬ Even z :=
-- proof
  even_sub_one.trans Int.not_even_iff_odd.symm

end OeisA108081

namespace OeisA108081

/--
[even_succ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma even_succ_iff
  {z : ℤ} :
-- imply
  Even (z + 1) ↔ ¬ Even z :=
-- proof
  even_add_one.trans Int.not_even_iff_odd.symm

end OeisA108081

namespace OeisA108081

/--
[rightChild_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma rightChild_pred
  {z : ℤ} :
-- imply
  rightChild (z - 1) = leftChild z - 1 := by
-- proof
  simp only [rightChild, leftChild]
  by_cases h : Even z
  · rw [if_pos h, if_neg ((even_pred_iff z).not.mpr (not_not.mpr h))] <;> ring
  · rw [if_neg h, if_pos ((even_pred_iff z).mpr h)] <;> ring

end OeisA108081

namespace OeisA108081

/--
[leftChild_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma leftChild_pred
  {z : ℤ} :
-- imply
  leftChild (z - 1) = rightChild z - 1 := by
-- proof
  simp only [rightChild, leftChild]
  by_cases h : Even z
  · rw [if_pos h, if_neg ((even_pred_iff z).not.mpr (not_not.mpr h))] <;> ring
  · rw [if_neg h, if_pos ((even_pred_iff z).mpr h)] <;> ring

end OeisA108081

namespace OeisA108081

/--
[rightChild_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma rightChild_succ
  {z : ℤ} :
-- imply
  rightChild (z + 1) = leftChild z + 1 := by
-- proof
  simp only [rightChild, leftChild]
  by_cases h : Even z
  · rw [if_pos h, if_neg ((even_succ_iff z).not.mpr (not_not.mpr h))] <;> ring
  · rw [if_neg h, if_pos ((even_succ_iff z).mpr h)] <;> ring

end OeisA108081

namespace OeisA108081

/--
[leftChild_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma leftChild_succ
  {z : ℤ} :
-- imply
  leftChild (z + 1) = rightChild z + 1 := by
-- proof
  simp only [rightChild, leftChild]
  by_cases h : Even z
  · rw [if_pos h, if_neg ((even_succ_iff z).not.mpr (not_not.mpr h))] <;> ring
  · rw [if_neg h, if_pos ((even_succ_iff z).mpr h)] <;> ring
@[simp] lemma leftChild_leftChild (z : ℤ) : leftChild (leftChild z) = z := by
  by_cases h : Even z
  · have hz : leftChild z = z - 1 := if_pos h
    rw [hz, leftChild_pred, rightChild, if_pos h]
    ring
  · have hz : leftChild z = z + 1 := if_neg h
    rw [hz, leftChild_succ, rightChild, if_neg h]
    ring
@[simp] lemma rightChild_rightChild (z : ℤ) : rightChild (rightChild z) = z := by
  by_cases h : Even z
  · have hz : rightChild z = z + 1 := if_pos h
    rw [hz, rightChild_succ, leftChild, if_pos h]
    ring
  · have hz : rightChild z = z - 1 := if_neg h
    rw [hz, rightChild_pred, leftChild, if_neg h]
    ring

end OeisA108081

namespace OeisA108081

/--
[Expand.toCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma Expand.toCoord
  {u v : Word}
-- given
  (h : Expand u v) :
-- imply
  CoordExpand (coordWord u) (coordWord v) := by
-- proof
  cases h with
  | left p s z =>
    simpa [coordWord, List.map_append] using
      CoordExpand.left (coordWord p) (coordWord s) (edgeCoord z)
  | right p s z =>
    simpa [coordWord, List.map_append] using
      CoordExpand.right (coordWord p) (coordWord s) (edgeCoord z)

end OeisA108081

namespace OeisA108081

/--
[CoordExpand.toExpand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordExpand.toExpand
  {u v : List EdgeCoord}
-- given
  (h : CoordExpand u v) :
-- imply
  Expand (u.map edgeValue) (v.map edgeValue) := by
-- proof
  cases h with
  | left p s q =>
    simpa [List.map_append] using
      Expand.left (p.map edgeValue) (s.map edgeValue) (edgeValue q)
  | right p s q =>
    simpa [List.map_append] using
      Expand.right (p.map edgeValue) (s.map edgeValue) (edgeValue q)

end OeisA108081

namespace OeisA108081

/--
[Expand.with_context](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma Expand.with_context
  {u v : Word}
  {p s : Word}
-- given
  (h : Expand u v) :
-- imply
  Expand (p ++ u ++ s) (p ++ v ++ s) := by
-- proof
  cases h with
  | left q t z =>
    simpa only [List.append_assoc, List.cons_append] using
      Expand.left (p ++ q) (t ++ s) z
  | right q t z =>
    simpa only [List.append_assoc, List.cons_append] using
      Expand.right (p ++ q) (t ++ s) z

end OeisA108081

namespace OeisA108081

/--
[Expand.map_l](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma Expand.map_l
  {u v : Word}
-- given
  (h : Expand u v) :
-- imply
  Expand (l u) (l v) := by
-- proof
  cases h with
  | left p s z =>
    simpa [l, List.reverse_append, List.map_append, rightChild_pred,
      List.append_assoc] using Expand.right (l s) (l p) (z - 1)
  | right p s z =>
    simpa [l, List.reverse_append, List.map_append, leftChild_pred,
      List.append_assoc] using Expand.left (l s) (l p) (z - 1)

end OeisA108081

namespace OeisA108081

/--
[Expand.map_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma Expand.map_r
  {u v : Word}
-- given
  (h : Expand u v) :
-- imply
  Expand (r u) (r v) := by
-- proof
  cases h with
  | left p s z =>
    simpa [r, List.reverse_append, List.map_append, rightChild_succ,
      List.append_assoc] using Expand.right (r s) (r p) (z + 1)
  | right p s z =>
    simpa [r, List.reverse_append, List.map_append, leftChild_succ,
      List.append_assoc] using Expand.left (r s) (r p) (z + 1)

end OeisA108081

namespace OeisA108081

/--
[Expand.length_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma Expand.length_succ
  {u v : Word}
-- given
  (h : Expand u v) :
-- imply
  v.length = u.length + 1 := by
-- proof
  cases h <;> simp <;> omega

end OeisA108081

namespace OeisA108081

/--
[expand_base_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma expand_base_left
-- imply
  Expand ([0] : Word) [-1, 0] := by
-- proof
  simpa using Expand.left [] [] 0

end OeisA108081

namespace OeisA108081

/--
[expand_base_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma expand_base_right
-- imply
  Expand ([0] : Word) [0, 1] := by
-- proof
  simpa using Expand.right [] [] 0

end OeisA108081

namespace OeisA108081

/--
[adjacent_coordLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma adjacent_coordLeft
  {q : EdgeCoord} :
-- imply
  CoordAdjacent (coordLeft q) q := by
-- proof
  obtain ⟨k, e⟩ := q
  cases e <;> simp [CoordAdjacent, coordLeft, rightIndex]

end OeisA108081

namespace OeisA108081

/--
[adjacent_coordRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma adjacent_coordRight
  {q : EdgeCoord} :
-- imply
  CoordAdjacent q (coordRight q) := by
-- proof
  obtain ⟨k, e⟩ := q
  cases e <;> simp [CoordAdjacent, coordRight, rightIndex]

end OeisA108081

namespace OeisA108081

/--
[adjacent_coordRight_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma adjacent_coordRight_iff
  {q s : EdgeCoord} :
-- imply
  CoordAdjacent (coordRight q) s ↔ CoordAdjacent q s := by
-- proof
  obtain ⟨k, e⟩ := q
  cases e <;> simp [CoordAdjacent, coordRight, rightIndex] <;> omega

end OeisA108081

namespace OeisA108081

/--
[adjacent_coordLeft_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma adjacent_coordLeft_iff
  {p q : EdgeCoord} :
-- imply
  CoordAdjacent p (coordLeft q) ↔ CoordAdjacent p q := by
-- proof
  obtain ⟨k, e⟩ := q
  cases e <;> simp [CoordAdjacent, coordLeft]
@[simp] lemma fst_coordLeft (q : EdgeCoord) : (coordLeft q).1 = q.1 := by
  obtain ⟨k, e⟩ := q
  cases e <;> rfl
@[simp] lemma rightIndex_coordRight (q : EdgeCoord) :
  rightIndex (coordRight q) = rightIndex q := by
  obtain ⟨k, e⟩ := q
  cases e <;> simp [coordRight, rightIndex]

end OeisA108081

namespace OeisA108081

/--
[CoordPath.prepend_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordPath.prepend_left
  {q : EdgeCoord}
  {s : List EdgeCoord}
-- given
  (h : CoordPath (q :: s)) :
-- imply
  CoordPath (coordLeft q :: q :: s) :=
-- proof
  CoordPath.cons (adjacent_coordLeft q) h

end OeisA108081

namespace OeisA108081

/--
[CoordPath.append_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordPath.append_right
  {p : List EdgeCoord}
  {q : EdgeCoord}
-- given
  (h : CoordPath (p ++ [q])) :
-- imply
  CoordPath (p ++ [q, coordRight q]) := by
-- proof
  induction p with
  | nil =>
    simp only [List.nil_append] at h ⊢
    exact CoordPath.cons (adjacent_coordRight q) (CoordPath.singleton _)
  | cons x p ih =>
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons_append] at h ⊢
      cases h with
      | cons h₁ h₂ =>
        exact CoordPath.cons h₁
          (CoordPath.cons (adjacent_coordRight q) (CoordPath.singleton _))
    | cons y p =>
      simp only [List.cons_append] at h ⊢
      cases h with
      | cons hxy htail => exact CoordPath.cons hxy (ih htail)

end OeisA108081

namespace OeisA108081

/--
[CoordPath.expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordPath.expand
  {u v : List EdgeCoord}
-- given
  (hu : CoordPath u)
  (h : CoordExpand u v) :
-- imply
  CoordPath v := by
-- proof
  cases h with
  | left p s q =>
    induction p with
    | nil =>
      simpa only [List.nil_append] using hu.prepend_left
    | cons x p ih =>
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons_append] at hu ⊢
        cases hu with
        | cons hxq htail =>
          exact CoordPath.cons ((adjacent_coordLeft_iff x q).mpr hxq)
            htail.prepend_left
      | cons y p =>
        simp only [List.cons_append] at hu ⊢
        cases hu with
        | cons hxy htail => exact CoordPath.cons hxy (ih htail)
  | right p s q =>
    induction p with
    | nil =>
      simp only [List.nil_append] at hu ⊢
      cases s with
      | nil =>
        exact CoordPath.cons (adjacent_coordRight q) (CoordPath.singleton _)
      | cons r s =>
        cases hu with
        | cons hqr htail =>
          exact CoordPath.cons (adjacent_coordRight q)
            (CoordPath.cons ((adjacent_coordRight_iff q r).mpr hqr) htail)
    | cons x p ih =>
      cases p with
      | nil =>
        simp only [List.nil_append, List.cons_append] at hu ⊢
        cases hu with
        | cons hxq htail => exact CoordPath.cons hxq (ih htail)
      | cons y p =>
        simp only [List.cons_append] at hu ⊢
        cases hu with
        | cons hxy htail => exact CoordPath.cons hxy (ih htail)

end OeisA108081

namespace OeisA108081

/--
[CoordInsert.path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordInsert.path
  {w : List EdgeCoord}
-- given
  (hw : CoordInsert w) :
-- imply
  CoordPath w := by
-- proof
  induction hw with
  | refl => exact CoordPath.singleton _
  | tail _ h ih => exact ih.expand h

end OeisA108081

namespace OeisA108081

/--
[XInsert.toCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XInsert.toCoord
  {w : Word}
-- given
  (hw : XInsert w) :
-- imply
  CoordInsert (coordWord w) := by
-- proof
  simpa [XInsert, CoordInsert, coordWord, edgeCoord] using
    Relation.ReflTransGen.lift coordWord (fun _ _ h => h.toCoord) hw

end OeisA108081

namespace OeisA108081

/--
[CoordInsert.toXInsert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordInsert.toXInsert
  {w : List EdgeCoord}
-- given
  (hw : CoordInsert w) :
-- imply
  XInsert (w.map edgeValue) := by
-- proof
  simpa [XInsert, CoordInsert, edgeValue] using
    Relation.ReflTransGen.lift (List.map edgeValue) (fun _ _ h => h.toExpand) hw

end OeisA108081

namespace OeisA108081

/--
[coordInsert_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordInsert_iff
  {w : Word} :
-- imply
  CoordInsert (coordWord w) ↔ XInsert w := by
-- proof
  constructor
  · intro h
    have hx := h.toXInsert
    change XInsert ((coordWord w).map edgeValue) at hx
    rwa [map_edgeValue_coordWord] at hx
  · exact fun h => h.toCoord

end OeisA108081

namespace OeisA108081

/--
[XInsert.expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XInsert.expand
  {u v : Word}
-- given
  (hu : XInsert u)
  (h : Expand u v) :
-- imply
  XInsert v :=
-- proof
  hu.tail h

end OeisA108081

namespace OeisA108081

/--
[expandStar_with_context](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma expandStar_with_context
  {u v : Word}
  {p s : Word}
-- given
  (h : Relation.ReflTransGen Expand u v) :
-- imply
  Relation.ReflTransGen Expand (p ++ u ++ s) (p ++ v ++ s) :=
-- proof
  Relation.ReflTransGen.lift (fun w => p ++ w ++ s)
    (fun _ _ h' => h'.with_context p s) h

end OeisA108081

namespace OeisA108081

/--
[expandStar_map_l](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma expandStar_map_l
  {u v : Word}
-- given
  (h : Relation.ReflTransGen Expand u v) :
-- imply
  Relation.ReflTransGen Expand (l u) (l v) :=
-- proof
  Relation.ReflTransGen.lift l (fun _ _ h' => h'.map_l) h

end OeisA108081

namespace OeisA108081

/--
[expandStar_map_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma expandStar_map_r
  {u v : Word}
-- given
  (h : Relation.ReflTransGen Expand u v) :
-- imply
  Relation.ReflTransGen Expand (r u) (r v) :=
-- proof
  Relation.ReflTransGen.lift r (fun _ _ h' => h'.map_r) h

end OeisA108081

namespace OeisA108081

/--
[XWord.toXInsert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.toXInsert
  {w : Word}
-- given
  (hw : XWord w) :
-- imply
  XInsert w := by
-- proof
  induction hw with
  | base => exact XInsert.base
  | @step_left u v hu hv ihu ihv =>
    apply (XInsert.expand XInsert.base expand_base_left).trans
    have h₁ : Relation.ReflTransGen Expand ([-1, 0] : Word) (l u ++ [0]) := by
      simpa [l] using expandStar_with_context (expandStar_map_l ihu) [] [0]
    have h₂ : Relation.ReflTransGen Expand (l u ++ [0]) (l u ++ v) := by
      simpa using expandStar_with_context ihv (l u) []
    exact h₁.trans h₂
  | @step_right u v hu hv ihu ihv =>
    apply (XInsert.expand XInsert.base expand_base_right).trans
    have h₁ : Relation.ReflTransGen Expand ([0, 1] : Word) (u ++ [1]) := by
      simpa using expandStar_with_context ihu [] [1]
    have h₂ : Relation.ReflTransGen Expand (u ++ [1]) (u ++ r v) := by
      simpa [r] using expandStar_with_context (expandStar_map_r ihv) u []
    exact h₁.trans h₂

end OeisA108081

namespace OeisA108081

/--
[XWord.expand_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.expand_pair
  {w : Word}
-- given
  (hw : XWord w) :
-- imply
  (∀ (p s : Word) (z : ℤ), w = p ++ z :: s → XWord (p ++ leftChild z :: z :: s)) ∧ (∀ (p s : Word) (z : ℤ), w = p ++ z :: s → XWord (p ++ z :: rightChild z :: s)) := by
-- proof
  induction hw with
  | base =>
    constructor <;> intro p s z heq
    all_goals
      have hlen := congrArg List.length heq
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have hp : p = [] := List.length_eq_zero_iff.mp (by omega)
      have hs : s = [] := List.length_eq_zero_iff.mp (by omega)
      subst p; subst s
      simp only [List.nil_append, List.cons.injEq, and_true] at heq
      subst z
    · simpa [l] using XWord.step_left XWord.base XWord.base
    · simpa [r] using XWord.step_right XWord.base XWord.base
  | @step_left u v hu hv ihu ihv =>
    constructor
    · intro p s z heq
      obtain ⟨q, hp, hvq⟩ | ⟨q, hlu, hsq⟩ := List.append_eq_append_iff.mp heq
      · have hnew := XWord.step_left hu (ihv.1 q s z hvq)
        simpa [hp, List.append_assoc] using hnew
      · cases q with
        | nil =>
          simp only [List.append_nil] at hlu
          subst p
          have hnew := XWord.step_left hu (ihv.1 [] s z hsq.symm)
          simpa using hnew
        | cons b q =>
          simp only [List.cons_append, List.cons.injEq] at hsq
          obtain ⟨rfl, rfl⟩ := hsq
          have heqU : u = r q ++ (z + 1) :: r p := by
            have hrr := congrArg r hlu
            rw [r_l] at hrr
            simpa [r, List.reverse_append, List.map_append, List.append_assoc] using hrr
          have hnew := XWord.step_left (ihu.2 (r q) (r p) (z + 1) heqU) hv
          simpa [l, r, Function.comp_def, List.reverse_append, List.map_append, List.append_assoc,
            rightChild_succ] using hnew
    · intro p s z heq
      obtain ⟨q, hp, hvq⟩ | ⟨q, hlu, hsq⟩ := List.append_eq_append_iff.mp heq
      · have hnew := XWord.step_left hu (ihv.2 q s z hvq)
        simpa [hp, List.append_assoc] using hnew
      · cases q with
        | nil =>
          simp only [List.append_nil] at hlu
          subst p
          have hnew := XWord.step_left hu (ihv.2 [] s z hsq.symm)
          simpa using hnew
        | cons b q =>
          simp only [List.cons_append, List.cons.injEq] at hsq
          obtain ⟨rfl, rfl⟩ := hsq
          have heqU : u = r q ++ (z + 1) :: r p := by
            have hrr := congrArg r hlu
            rw [r_l] at hrr
            simpa [r, List.reverse_append, List.map_append, List.append_assoc] using hrr
          have hnew := XWord.step_left (ihu.1 (r q) (r p) (z + 1) heqU) hv
          simpa [l, r, Function.comp_def, List.reverse_append, List.map_append, List.append_assoc,
            leftChild_succ] using hnew
  | @step_right u v hu hv ihu ihv =>
    constructor
    · intro p s z heq
      obtain ⟨q, hp, hrv⟩ | ⟨q, huq, hsq⟩ := List.append_eq_append_iff.mp heq
      · have heqV : v = l s ++ (z - 1) :: l q := by
        have hll := congrArg l hrv
        rw [l_r] at hll
        simpa [l, List.reverse_append, List.map_append, List.append_assoc] using hll
        have hnew := XWord.step_right hu (ihv.2 (l s) (l q) (z - 1) heqV)
        simpa [hp, l, r, Function.comp_def, List.reverse_append, List.map_append, List.append_assoc,
          rightChild_pred] using hnew
      · cases q with
        | nil =>
          simp only [List.append_nil] at huq
          subst p
          have heqV : v = l s ++ [z - 1] := by
            have hsq' : z :: s = r v := by simpa using hsq
            have hll := congrArg l hsq'.symm
            rw [l_r] at hll
            simpa [l, List.reverse_append, List.map_append, List.append_assoc] using hll
          have hnew := XWord.step_right hu (ihv.2 (l s) [] (z - 1) heqV)
          simpa [l, r, Function.comp_def, List.reverse_append, List.map_append, List.append_assoc,
            rightChild_pred] using hnew
        | cons b q =>
          simp only [List.cons_append, List.cons.injEq] at hsq
          obtain ⟨rfl, rfl⟩ := hsq
          have hnew := XWord.step_right (ihu.1 p q z huq) hv
          simpa [List.append_assoc] using hnew
    · intro p s z heq
      obtain ⟨q, hp, hrv⟩ | ⟨q, huq, hsq⟩ := List.append_eq_append_iff.mp heq
      · have heqV : v = l s ++ (z - 1) :: l q := by
        have hll := congrArg l hrv
        rw [l_r] at hll
        simpa [l, List.reverse_append, List.map_append, List.append_assoc] using hll
        have hnew := XWord.step_right hu (ihv.1 (l s) (l q) (z - 1) heqV)
        simpa [hp, l, r, Function.comp_def, List.reverse_append, List.map_append, List.append_assoc,
          leftChild_pred] using hnew
      · cases q with
        | nil =>
          simp only [List.append_nil] at huq
          subst p
          have heqV : v = l s ++ [z - 1] := by
            have hsq' : z :: s = r v := by simpa using hsq
            have hll := congrArg l hsq'.symm
            rw [l_r] at hll
            simpa [l, List.reverse_append, List.map_append, List.append_assoc] using hll
          have hnew := XWord.step_right hu (ihv.1 (l s) [] (z - 1) heqV)
          simpa [l, r, Function.comp_def, List.reverse_append, List.map_append, List.append_assoc,
            leftChild_pred] using hnew
        | cons b q =>
          simp only [List.cons_append, List.cons.injEq] at hsq
          obtain ⟨rfl, rfl⟩ := hsq
          have hnew := XWord.step_right (ihu.2 p q z huq) hv
          simpa [List.append_assoc] using hnew

end OeisA108081

namespace OeisA108081

/--
[XWord.expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.expand
  {u v : Word}
-- given
  (hu : XWord u)
  (h : Expand u v) :
-- imply
  XWord v := by
-- proof
  cases h with
  | left p s z => exact hu.expand_pair.1 p s z rfl
  | right p s z => exact hu.expand_pair.2 p s z rfl

end OeisA108081

namespace OeisA108081

/--
[XInsert.toXWord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XInsert.toXWord
  {w : Word}
-- given
  (hw : XInsert w) :
-- imply
  XWord w := by
-- proof
  induction hw with
  | refl => exact XWord.base
  | tail _ h ih => exact ih.expand h

end OeisA108081

namespace OeisA108081

/--
[xWord_iff_xInsert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma xWord_iff_xInsert
  {w : Word} :
-- imply
  XWord w ↔ XInsert w :=
-- proof
  ⟨XWord.toXInsert, XInsert.toXWord⟩

end OeisA108081

namespace OeisA108081

/--
[XWord.exists_expand_predecessor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.exists_expand_predecessor
  {w : Word}
-- given
  (hw : XWord w)
  (hlen : 1 < w.length) :
-- imply
  ∃ u : Word, XWord u ∧ Expand u w := by
-- proof
  obtain h | ⟨u, hu, he⟩ := Relation.ReflTransGen.cases_tail hw.toXInsert
  · subst w
    simp at hlen
  · exact ⟨u, XInsert.toXWord hu, he⟩

end OeisA108081

namespace OeisA108081

/--
[XWord.prepend_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.prepend_neg_one
  {w : Word}
-- given
  (hw : XWord w) :
-- imply
  XWord ((-1 : ℤ) :: w) := by
-- proof
  simpa [l] using XWord.step_left XWord.base hw

end OeisA108081

namespace OeisA108081

/--
[XWord.append_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.append_one
  {w : Word}
-- given
  (hw : XWord w) :
-- imply
  XWord (w ++ [(1 : ℤ)]) := by
-- proof
  simpa [r] using XWord.step_right hw XWord.base

end OeisA108081

namespace OeisA108081

/--
[XWord.zero_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.zero_mem
  {w : Word}
-- given
  (hw : XWord w) :
-- imply
  (0 : ℤ) ∈ w := by
-- proof
  induction hw with
  | base => simp
  | step_left hu hv ihu ihv => exact List.mem_append_right _ ihv
  | step_right hu hv ihu ihv => exact List.mem_append_left _ ihu

end OeisA108081

namespace OeisA108081

/--
[XWord.length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.length_pos
  {w : Word}
-- given
  (hw : XWord w) :
-- imply
  0 < w.length := by
-- proof
  induction hw with
  | base => simp
  | step_left hu hv ihu ihv => simp [ihu, ihv]
  | step_right hu hv ihu ihv => simp [ihu, ihv]

end OeisA108081

namespace OeisA108081

/--
[XWord.value_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.value_bounds
  {w : Word}
  {z : ℤ}
-- given
  (hw : XWord w)
  (hz : z ∈ w) :
-- imply
  -(w.length : ℤ) ≤ z ∧ z ≤ (w.length : ℤ) := by
-- proof
  induction hw generalizing z with
  | base => simp_all
  | @step_left u v hu hv ihu ihv =>
    simp only [List.mem_append] at hz
    obtain hz | hz := hz
    · have hzu : z + 1 ∈ u := mem_l_iff.mp hz
      have hb := ihu hzu
      simp only [length_l, List.length_append, Nat.cast_add]
      have hvlen := XWord.length_pos hv
      omega
    · have hb := ihv hz
      simp only [length_l, List.length_append, Nat.cast_add]
      have hulen := XWord.length_pos hu
      omega
  | @step_right u v hu hv ihu ihv =>
    simp only [List.mem_append] at hz
    obtain hz | hz := hz
    · have hb := ihu hz
      simp only [length_r, List.length_append, Nat.cast_add]
      have hvlen := XWord.length_pos hv
      omega
    · have hzv : z - 1 ∈ v := mem_r_iff.mp hz
      have hb := ihv hzv
      simp only [length_r, List.length_append, Nat.cast_add]
      have hulen := XWord.length_pos hu
      omega

end OeisA108081

namespace OeisA108081

/--
[XWord.endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.endpoints
  {w : Word}
-- given
  (hw : XWord w) :
-- imply
  (w.head? = some (-1 : ℤ) ∨ w.head? = some 0) ∧ (w.getLast? = some 0 ∨ w.getLast? = some 1) := by
-- proof
  induction hw with
  | base => simp
  | step_left hu hv ihu ihv =>
    obtain ⟨huf | huf, hul | hul⟩ <;> := ihu
      obtain ⟨hvf | hvf, hvl | hvl⟩ <;> := ihv
      simp_all [l, List.head?_append, List.getLast?_append]
  | step_right hu hv ihu ihv =>
    obtain ⟨huf | huf, hul | hul⟩ <;> := ihu
      obtain ⟨hvf | hvf, hvl | hvl⟩ <;> := ihv
      simp_all [r, List.head?_append, List.getLast?_append]

end OeisA108081

namespace OeisA108081

/--
[coordWord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordWord_injective
-- imply
  Function.Injective coordWord := by
-- proof
  intro u
  induction u with
  | nil =>
    intro v h
    cases v <;> simp_all [coordWord]
  | cons x u ih =>
    intro v h
    cases v with
    | nil => simp [coordWord] at h
    | cons y v =>
      simp only [coordWord, List.map_cons, List.cons.injEq] at h
      obtain ⟨hxy, huv⟩ := h
      have : x = y := by
        have := congrArg edgeValue hxy
        simpa using this
      subst y
      rw [ih huv]

end OeisA108081

namespace OeisA108081

/--
[XWord.coord_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.coord_endpoints
  {w : Word}
-- given
  (hw : XWord w) :
-- imply
  ((coordWord w).head? = some (0, true) ∨ (coordWord w).head? = some (0, false)) ∧ ((coordWord w).getLast? = some (0, false) ∨ (coordWord w).getLast? = some (1, true)) := by
-- proof
  obtain ⟨hf | hf, hl | hl⟩ <;> := hw.endpoints
    simp_all [coordWord, edgeCoord]

end OeisA108081

namespace OeisA108081

/--
[CoordInsert.forestForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordInsert.forestForm
  {w : List EdgeCoord}
-- given
  (hw : CoordInsert w) :
-- imply
  CoordForestForm (0, false) w := by
-- proof
  have hx : XWord (w.map edgeValue) := xWord_iff_xInsert.mpr hw.toXInsert
  have he := hx.coord_endpoints
  rw [coordWord_map_edgeValue] at he
  right
  refine ⟨hw.path, ?_, ?_⟩
  · rcases he.1 with hf | hf <;> simp_all
  · rcases he.2 with hl | hl <;> simp_all [rightIndex]

end OeisA108081

namespace OeisA108081

/--
[image_coordWord_xN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma image_coordWord_xN
  {n : ℕ} :
-- imply
  coordWord '' xN n = coordXN n := by
-- proof
  ext q
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [xN, Set.mem_setOf_eq] at hw
    rw [coordXN, Set.mem_setOf_eq]
    refine ⟨coordInsert_iff.mpr (xWord_iff_xInsert.mp hw.1), ?_⟩
    simpa [coordWord] using hw.2
  · intro hq
    rw [coordXN, Set.mem_setOf_eq] at hq
    let w : Word := q.map edgeValue
    have hwins : XInsert w := hq.1.toXInsert
    have hwlen : w.length = n := by simpa [w] using hq.2
    refine ⟨w, ?_, ?_⟩
    · rw [xN, Set.mem_setOf_eq]
      exact ⟨xWord_iff_xInsert.mpr hwins, hwlen⟩
    · exact coordWord_map_edgeValue q

end OeisA108081

namespace OeisA108081

/--
[ncard_coordXN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_coordXN
  {n : ℕ} :
-- imply
  (coordXN n).ncard = (xN n).ncard := by
-- proof
  rw [← image_coordWord_xN]
  exact Set.ncard_image_of_injective (xN n) coordWord_injective

end OeisA108081

namespace OeisA108081

/--
[finite_bounded_words](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma finite_bounded_words
  {n : ℕ} :
-- imply
  Set.Finite {w : Word | w.length = n ∧ ∀ z ∈ w, -(n : ℤ) ≤ z ∧ z ≤ (n : ℤ)} := by
-- proof
  let B : Set ℤ := Set.Icc (-(n : ℤ)) (n : ℤ)
  have hB : B.Finite := Set.finite_Icc _ _
  let P : Set Word := {w | w.length = n ∧ ∀ z ∈ w, z ∈ B}
  have hP : P.Finite := by
    let F : P → List.Vector B n := fun w =>
      ⟨w.1.attachWith (fun z => z ∈ B) w.2.2, by simp [w.2.1]⟩
    letI : Finite B := hB.to_subtype
    have hi : Function.Injective F := by
      intro x y h
      apply Subtype.ext
      have hh := congrArg (fun q => q.1.map (fun z : B => z.1)) h
      simpa [F] using hh
    letI : Finite P := Finite.of_injective F hi
    exact Set.toFinite P
  simpa [P, B] using hP

end OeisA108081

namespace OeisA108081

/--
[xN_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma xN_finite
  {n : ℕ} :
-- imply
  (xN n).Finite := by
-- proof
  apply (finite_bounded_words n).subset
  intro w hw
  rw [Set.mem_setOf_eq]
  rw [xN, Set.mem_setOf_eq] at hw
  refine ⟨hw.2, fun z hz => ?_⟩
  simpa [hw.2] using hw.1.value_bounds hz

end OeisA108081

namespace OeisA108081

/--
[XWord.length_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.length_one
  {w : Word}
-- given
  (hw : XWord w)
  (hlen : w.length = 1) :
-- imply
  w = [0] := by
-- proof
  induction hw with
  | base => rfl
  | @step_left u v hu hv ihu ihv =>
    have hu' := hu.length_pos
    have hv' := hv.length_pos
    simp only [length_l, List.length_append] at hlen
    omega
  | @step_right u v hu hv ihu ihv =>
    have hu' := hu.length_pos
    have hv' := hv.length_pos
    simp only [length_r, List.length_append] at hlen
    omega

end OeisA108081

namespace OeisA108081

/--
[XWord.length_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma XWord.length_two
  {w : Word}
-- given
  (hw : XWord w)
  (hlen : w.length = 2) :
-- imply
  w = [(-1 : ℤ), 0] ∨ w = [0, 1] := by
-- proof
  induction hw with
  | base => simp at hlen
  | @step_left u v hu hv ihu ihv =>
    have hu' := hu.length_pos
    have hv' := hv.length_pos
    have huv : u.length + v.length = 2 := by simpa using hlen
    have hulu : u.length = 1 := by omega
    have hvlu : v.length = 1 := by omega
    rw [hu.length_one hulu, hv.length_one hvlu]
    simp [l]
  | @step_right u v hu hv ihu ihv =>
    have hu' := hu.length_pos
    have hv' := hv.length_pos
    have huv : u.length + v.length = 2 := by simpa using hlen
    have hulu : u.length = 1 := by omega
    have hvlu : v.length = 1 := by omega
    rw [hu.length_one hulu, hv.length_one hvlu]
    simp [r]

end OeisA108081

namespace OeisA108081

/--
[xN_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma xN_two
-- imply
  xN 2 = {([(-1 : ℤ), 0] : Word), [0, 1]} := by
-- proof
  ext w
  simp only [xN, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hlen⟩
    exact hw.length_two hlen
  · rintro (rfl | rfl)
    · exact ⟨XWord.prepend_neg_one XWord.base, rfl⟩
    · exact ⟨XWord.append_one XWord.base, rfl⟩

end OeisA108081

namespace OeisA108081

/--
[ncard_xN_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_xN_two
-- imply
  (xN 2).ncard = 2 := by
-- proof
  rw [xN_two]
  norm_num

end OeisA108081

namespace OeisA108081

/--
[a_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma a_one
-- imply
  a 1 = 2 := by
-- proof
  decide

end OeisA108081

namespace OeisA108081

/--
[xN_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma xN_one
-- imply
  xN 1 = {([0] : Word)} := by
-- proof
  ext w
  simp only [xN, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hlen⟩
    exact hw.length_one hlen
  · rintro rfl
    exact ⟨XWord.base, rfl⟩

end OeisA108081

namespace OeisA108081

/--
[ncard_xN_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_xN_one
-- imply
  (xN 1).ncard = 1 := by
-- proof
  rw [xN_one]
  simp

end OeisA108081

namespace OeisA108081

/--
[a_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma a_zero
-- imply
  a 0 = 1 := by
-- proof
  simp [a]

end OeisA108081

namespace OeisA108081

/--
[bitStep_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitStep_eq
  {k : ℤ}
  {e y : Bool} :
-- imply
  bitStep k e y = k + 1 - (if e then 1 else 0) - (if y then 1 else 0) := by
-- proof
  cases e <;> cases y <;> simp [bitStep]

end OeisA108081

namespace OeisA108081

/--
[adjacent_bitStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma adjacent_bitStep
  {k : ℤ}
  {e y f : Bool} :
-- imply
  CoordAdjacent (k, e) (bitStep k e y, f) := by
-- proof
  cases e <;> cases y <;> simp [bitStep, CoordAdjacent, rightIndex]

end OeisA108081

namespace OeisA108081

/--
[path_bitsToCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma path_bitsToCoords
  {k : ℤ}
  {b : List Bool} :
-- imply
  CoordPath (bitsToCoords k b) := by
-- proof
  induction b using List.twoStepInduction generalizing k with
  | nil => exact CoordPath.nil
  | singleton e => exact CoordPath.singleton _
  | cons_cons e y b ih =>
    cases b with
    | nil =>
      simp only [bitsToCoords_cons]
      exact CoordPath.singleton _
    | cons f cs =>
      simp only [bitsToCoords_cons]
      exact CoordPath.cons (adjacent_bitStep k e y f)
        (by simpa only [bitsToCoords_cons] using ih (bitStep k e y))

end OeisA108081

namespace OeisA108081

/--
[length_bitsToCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma length_bitsToCoords
  {k : ℤ}
  {b : List Bool} :
-- imply
  (bitsToCoords k b).length = (b.length + 1) / 2 := by
-- proof
  induction b using List.twoStepInduction generalizing k with
  | nil => simp [bitsToCoords]
  | singleton e => simp [bitsToCoords]
  | cons_cons e y b ih =>
    simp only [bitsToCoords, List.length_cons]
    rw [ih]
    omega

end OeisA108081

namespace OeisA108081

/--
[head_bitsToCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma head_bitsToCoords
  {k : ℤ}
  {e : Bool}
  {b : List Bool} :
-- imply
  (bitsToCoords k (e :: b)).head? = some (k, e) := by
-- proof
  rw [bitsToCoords_cons]
  rfl

end OeisA108081

namespace OeisA108081

/--
[last_bitsToCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma last_bitsToCoords
  {k : ℤ}
  {e : Bool} :
-- imply
  (bitsToCoords k [e]).getLast? = some (k, e) := by
-- proof
  rfl

end OeisA108081

namespace OeisA108081

/--
[rightIndex_last_bitsToCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma rightIndex_last_bitsToCoords
  {k : ℤ}
  {m : ℕ}
  {b : List Bool}
-- given
  (hlen : b.length = 2 * m + 1) :
-- imply
  (bitsToCoords k b).getLast?.map rightIndex = some (k + (m : ℤ) - (b.count true : ℤ)) := by
-- proof
  induction m generalizing k b with
  | zero =>
    have hb : ∃ e, b = [e] := by
      cases b with
      | nil => simp at hlen
      | cons e t =>
        cases t with
        | nil => exact ⟨e, rfl⟩
        | cons f t => simp at hlen
    obtain ⟨e, rfl⟩ := hb
    cases e <;> simp [bitsToCoords, rightIndex]
  | succ m ih =>
    cases b with
    | nil => simp at hlen
    | cons e t =>
      cases t with
      | nil => simp at hlen
      | cons y cs =>
        have hcs : cs.length = 2 * m + 1 := by simp at hlen ⊢; omega
        cases cs with
        | nil => simp at hcs
        | cons f ds =>
          rw [bitsToCoords_cons]
          have hne : bitsToCoords (bitStep k e y) (f :: ds) ≠ [] := by
            rw [bitsToCoords_cons]
            simp
          rw [List.getLast?_cons_of_ne_nil hne]
          rw [ih (bitStep k e y) (f :: ds) hcs]
          cases e <;> cases y <;> simp [bitStep]
          all_goals omega

end OeisA108081

namespace OeisA108081

/--
[bitsToCoords_forestForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitsToCoords_forestForm
  {m : ℕ}
  {b : List Bool}
-- given
  (hb : b ∈ ForestBits m) :
-- imply
  CoordForestForm (0, false) (bitsToCoords 0 b) := by
-- proof
  rw [ForestBits, Set.mem_setOf_eq] at hb
  right
  refine ⟨path_bitsToCoords 0 b, ?_, ?_⟩
  · cases b with
    | nil => simp at hb
    | cons e t => cases e <;> simp [bitsToCoords]
  · rw [rightIndex_last_bitsToCoords 0 m b hb.1, hb.2]
    simp [rightIndex]

end OeisA108081

namespace OeisA108081

/--
[bitStep_coordMovementBit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitStep_coordMovementBit
  {q r : EdgeCoord}
-- given
  (h : CoordAdjacent q r) :
-- imply
  bitStep q.1 q.2 (coordMovementBit q r) = r.1 := by
-- proof
  obtain ⟨k, e⟩ := q
  obtain ⟨j, f⟩ := r
  cases e <;> simp [CoordAdjacent, rightIndex] at h <;>
    simp [coordMovementBit, bitStep] <;> omega

end OeisA108081

namespace OeisA108081

/--
[coordMovementBit_bitStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordMovementBit_bitStep
  {k : ℤ}
  {e y f : Bool} :
-- imply
  coordMovementBit (k, e) (bitStep k e y, f) = y := by
-- proof
  cases e <;> cases y <;> simp [coordMovementBit, bitStep]

end OeisA108081

namespace OeisA108081

/--
[coordsToBits_bitsToCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordsToBits_bitsToCoords
  {k : ℤ}
  {m : ℕ}
  {b : List Bool}
-- given
  (hlen : b.length = 2 * m + 1) :
-- imply
  coordsToBits (bitsToCoords k b) = b := by
-- proof
  induction m generalizing k b with
  | zero =>
    cases b with
    | nil => simp at hlen
    | cons e t =>
      cases t with
      | nil => simp [bitsToCoords, coordsToBits]
      | cons y t => simp at hlen
  | succ m ih =>
    cases b with
    | nil => simp at hlen
    | cons e t =>
      cases t with
      | nil => simp at hlen
      | cons y cs =>
        have hcs : cs.length = 2 * m + 1 := by simp at hlen ⊢; omega
        cases cs with
        | nil => simp at hcs
        | cons f ds =>
          simp only [bitsToCoords_cons, coordsToBits,
            coordMovementBit_bitStep]
          rw [← bitsToCoords_cons]
          rw [ih (bitStep k e y) (f :: ds) hcs]

end OeisA108081

namespace OeisA108081

/--
[bitsToCoords_coordsToBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitsToCoords_coordsToBits
  {w : List EdgeCoord}
-- given
  (hw : CoordPath w) :
-- imply
  bitsToCoords ((w.head?.map Prod.fst).getD 0) (coordsToBits w) = w := by
-- proof
  induction hw with
  | nil => rfl
  | singleton q =>
    obtain ⟨k, e⟩ := q
    simp [coordsToBits, bitsToCoords]
  | @cons q r s hqr hrs ih =>
    obtain ⟨k, e⟩ := q
    obtain ⟨j, f⟩ := r
    simp only [coordsToBits, List.head?_cons, Option.map_some, Option.getD_some,
      bitsToCoords_cons]
    rw [bitStep_coordMovementBit hqr]
    have hhead : ((j, f) :: s).head?.map Prod.fst = some j := by simp
    rw [show bitsToCoords j (coordsToBits ((j, f) :: s)) = (j, f) :: s by
      simpa [hhead] using ih]

end OeisA108081

namespace OeisA108081

/--
[length_coordsToBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma length_coordsToBits
  {w : List EdgeCoord}
-- given
  (hw : CoordPath w) :
-- imply
  (coordsToBits w).length = 2 * w.length - 1 := by
-- proof
  induction hw with
  | nil => simp [coordsToBits]
  | singleton q => simp [coordsToBits]
  | @cons q r s hqr hrs ih =>
    simp only [coordsToBits, List.length_cons]
    have hlenrs : (r :: s).length = s.length + 1 := rfl
    omega

end OeisA108081

namespace OeisA108081

/--
[count_coordsToBits_of_forestForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma count_coordsToBits_of_forestForm
  {m : ℕ}
  {w : List EdgeCoord}
-- given
  (hlen : w.length = m + 1)
  (hw : CoordForestForm (0, false) w) :
-- imply
  (coordsToBits w).count true = m := by
-- proof
  obtain rfl | ⟨hpath, hhead, hlast⟩ := hw
  · simp at hlen
  have hbitlen : (coordsToBits w).length = 2 * m + 1 := by
    rw [length_coordsToBits hpath, hlen]
    omega
  have hdecode := rightIndex_last_bitsToCoords 0 m (coordsToBits w) hbitlen
  have hfirst : (w.head?.map Prod.fst).getD 0 = 0 := by rw [hhead]; rfl
  have hdecode_eq : bitsToCoords 0 (coordsToBits w) = w := by
    rw [← hfirst]
    exact bitsToCoords_coordsToBits hpath
  rw [hdecode_eq, hlast] at hdecode
  simp [rightIndex] at hdecode
  omega

end OeisA108081

namespace OeisA108081

/--
[coordsToBits_mem_forestBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordsToBits_mem_forestBits
  {m : ℕ}
  {w : List EdgeCoord}
-- given
  (hlen : w.length = m + 1)
  (hw : CoordForestForm (0, false) w) :
-- imply
  coordsToBits w ∈ ForestBits m := by
-- proof
  rw [ForestBits, Set.mem_setOf_eq]
  refine ⟨?_, count_coordsToBits_of_forestForm hlen hw⟩
  obtain rfl | ⟨hpath, hhead, hlast⟩ := hw
  · simp at hlen
  · rw [length_coordsToBits hpath, hlen]
    omega

end OeisA108081

namespace OeisA108081

/--
[count_subsetBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma count_subsetBits
  {N : ℕ}
  {s : Finset (Fin N)} :
-- imply
  (subsetBits N s).count true = s.card := by
-- proof
  let f : Fin N → Bool := fun i => decide (i ∈ s)
  let v : List.Vector Bool N := List.Vector.ofFn f
  have h := Fin.card_filter_univ_eq_vector_get_eq_count true v
  have hv : v.toList = subsetBits N s := by simp [v, subsetBits, f]
  rw [hv] at h
  rw [← h]
  congr 1
  ext i
  simp [v, f]

end OeisA108081

namespace OeisA108081

/--
[subsetBits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma subsetBits_injective
  {N : ℕ} :
-- imply
  Function.Injective (subsetBits N) := by
-- proof
  intro s t h
  have hf : (fun i : Fin N => decide (i ∈ s)) =
    fun i => decide (i ∈ t) := by
    apply List.ofFn_injective
    simpa [subsetBits] using h
  ext i
  have hi := congrFun hf i
  simpa using hi

end OeisA108081

namespace OeisA108081

/--
[image_subsetBits_powersetCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma image_subsetBits_powersetCard
  {m : ℕ} :
-- imply
  subsetBits (2 * m + 1) '' (↑((Finset.univ : Finset (Fin (2 * m + 1))).powersetCard m) : Set (Finset (Fin (2 * m + 1)))) = ForestBits m := by
-- proof
  ext b
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [ForestBits, Set.mem_setOf_eq]
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    exact ⟨length_subsetBits _ _, by rw [count_subsetBits, hs.2]⟩
  · intro hb
    rw [ForestBits, Set.mem_setOf_eq] at hb
    let v : List.Vector Bool (2 * m + 1) := ⟨b, hb.1⟩
    let s : Finset (Fin (2 * m + 1)) := {i | v.get i = true}
    have hscard : s.card = m := by
      rwa [Fin.card_filter_univ_eq_vector_get_eq_count true v]
    refine ⟨s, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hscard⟩
    · have hf : (fun i : Fin (2 * m + 1) => decide (i ∈ s)) =
      fun i => v.get i := by
      funext i
      simp [s]
      rw [subsetBits, hf]
      calc
        List.ofFn (fun i => v.get i) = (List.Vector.ofFn (fun i => v.get i)).toList :=
          (List.Vector.toList_ofFn _).symm
        _ = v.toList := congrArg List.Vector.toList (List.Vector.ofFn_get v)
        _ = b := rfl

end OeisA108081

namespace OeisA108081

/--
[ncard_forestBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_forestBits
  {m : ℕ} :
-- imply
  (ForestBits m).ncard = (2 * m + 1).choose m := by
-- proof
  rw [← image_subsetBits_powersetCard]
  rw [Set.ncard_image_of_injective _ (subsetBits_injective _)]
  simp [Set.ncard_coe_finset, Finset.card_powersetCard]

end OeisA108081

namespace OeisA108081

/--
[image_bitsToCoords_forestBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma image_bitsToCoords_forestBits
  {m : ℕ} :
-- imply
  bitsToCoords 0 '' ForestBits m = coordForestXN m := by
-- proof
  ext w
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [coordForestXN, Set.mem_setOf_eq]
    refine ⟨bitsToCoords_forestForm hb, ?_⟩
    rw [length_bitsToCoords]
    rw [ForestBits, Set.mem_setOf_eq] at hb
    rw [hb.1]
    omega
  · intro hw
    rw [coordForestXN, Set.mem_setOf_eq] at hw
    refine ⟨coordsToBits w, coordsToBits_mem_forestBits hw.2 hw.1, ?_⟩
    obtain rfl | ⟨hpath, hhead, hlast⟩ := hw.1
    · simp at hw
    · have hfirst : (w.head?.map Prod.fst).getD 0 = 0 := by rw [hhead]; rfl
      rw [← hfirst]
      exact bitsToCoords_coordsToBits hpath

end OeisA108081

namespace OeisA108081

/--
[injOn_bitsToCoords_forestBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma injOn_bitsToCoords_forestBits
  {m : ℕ} :
-- imply
  Set.InjOn (bitsToCoords 0) (ForestBits m) := by
-- proof
  intro b hb c hc heq
  rw [ForestBits, Set.mem_setOf_eq] at hb hc
  rw [← coordsToBits_bitsToCoords 0 m b hb.1,
    ← coordsToBits_bitsToCoords 0 m c hc.1]
  exact congrArg coordsToBits heq

end OeisA108081

namespace OeisA108081

/--
[ncard_coordForestXN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_coordForestXN
  {m : ℕ} :
-- imply
  (coordForestXN m).ncard = (2 * m + 1).choose m := by
-- proof
  rw [← image_bitsToCoords_forestBits]
  rw [Set.ncard_image_of_injOn (injOn_bitsToCoords_forestBits m)]
  exact ncard_forestBits m

end OeisA108081

namespace OeisA108081

/--
[coordXN_subset_coordForestXN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordXN_subset_coordForestXN
  {m : ℕ} :
-- imply
  coordXN (m + 1) ⊆ coordForestXN m := by
-- proof
  intro w hw
  rw [coordXN, Set.mem_setOf_eq] at hw
  rw [coordForestXN, Set.mem_setOf_eq]
  exact ⟨hw.1.forestForm, hw.2⟩

end OeisA108081

namespace OeisA108081

/--
[forestBits_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma forestBits_finite
  {m : ℕ} :
-- imply
  (ForestBits m).Finite := by
-- proof
  rw [← image_subsetBits_powersetCard]
  exact (Finset.finite_toSet _).image _

end OeisA108081

namespace OeisA108081

/--
[coordForestXN_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordForestXN_finite
  {m : ℕ} :
-- imply
  (coordForestXN m).Finite := by
-- proof
  rw [← image_bitsToCoords_forestBits]
  exact (forestBits_finite m).image _

end OeisA108081

namespace OeisA108081

/--
[ncard_coordXN_le_choose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_coordXN_le_choose
  {m : ℕ} :
-- imply
  (coordXN (m + 1)).ncard ≤ (2 * m + 1).choose m := by
-- proof
  rw [← ncard_coordForestXN]
  exact Set.ncard_le_ncard (coordXN_subset_coordForestXN m) (coordForestXN_finite m)

end OeisA108081

namespace OeisA108081

/--
[bitsToCoords_coordsToBits_of_coordInsert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitsToCoords_coordsToBits_of_coordInsert
  {w : List EdgeCoord}
-- given
  (hw : CoordInsert w) :
-- imply
  bitsToCoords 0 (coordsToBits w) = w := by
-- proof
  have hp := hw.path
  have hf := hw.forestForm
  obtain hnil | ⟨_, hhead, _⟩ := hf
  · subst w
    rfl
  · have hk : (w.head?.map Prod.fst).getD 0 = 0 := by rw [hhead]; rfl
    rw [← hk]
    exact bitsToCoords_coordsToBits hp

end OeisA108081

namespace OeisA108081

/--
[TreeBits_subset_ForestBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma TreeBits_subset_ForestBits
  {m : ℕ} :
-- imply
  TreeBits m ⊆ ForestBits m := by
-- proof
  rintro b ⟨w, hw, rfl⟩
  rw [coordXN, Set.mem_setOf_eq] at hw
  exact coordsToBits_mem_forestBits hw.2 hw.1.forestForm

end OeisA108081

namespace OeisA108081

/--
[injOn_coordsToBits_coordXN](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma injOn_coordsToBits_coordXN
  {m : ℕ} :
-- imply
  Set.InjOn coordsToBits (coordXN (m + 1)) := by
-- proof
  intro u hu v hv h
  rw [coordXN, Set.mem_setOf_eq] at hu hv
  rw [← bitsToCoords_coordsToBits_of_coordInsert hu.1,
    ← bitsToCoords_coordsToBits_of_coordInsert hv.1, h]

end OeisA108081

namespace OeisA108081

/--
[ncard_TreeBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_TreeBits
  {m : ℕ} :
-- imply
  (TreeBits m).ncard = (coordXN (m + 1)).ncard := by
-- proof
  rw [TreeBits]
  exact Set.ncard_image_of_injOn (injOn_coordsToBits_coordXN m)

end OeisA108081

namespace OeisA108081

/--
[CoordTree.expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordTree.expand
  {root : EdgeCoord}
  {u v : List EdgeCoord}
-- given
  (hu : CoordTree root u)
  (h : CoordExpand u v) :
-- imply
  CoordTree root v :=
-- proof
  hu.tail h

end OeisA108081

namespace OeisA108081

/--
[CoordForest.ofTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForest.ofTree
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (h : CoordTree root w) :
-- imply
  CoordForest root w := by
-- proof
  simpa using CoordForest.cons h (CoordForest.nil : CoordForest root [])

end OeisA108081

namespace OeisA108081

/--
[CoordForest.append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForest.append
  {root : EdgeCoord}
  {u v : List EdgeCoord}
-- given
  (hu : CoordForest root u)
  (hv : CoordForest root v) :
-- imply
  CoordForest root (u ++ v) := by
-- proof
  induction hu generalizing v with
  | nil => simpa
  | @cons x y hx hy ih =>
    simpa [List.append_assoc] using CoordForest.cons hx (ih hv)

end OeisA108081

namespace OeisA108081

/--
[CoordForest.expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForest.expand
  {root : EdgeCoord}
  {u v : List EdgeCoord}
-- given
  (hu : CoordForest root u)
  (h : CoordExpand u v) :
-- imply
  CoordForest root v := by
-- proof
  have left_aux : ∀ (z : List EdgeCoord), CoordForest root z →
    ∀ (p s : List EdgeCoord) (q : EdgeCoord), z = p ++ q :: s →
      CoordForest root (p ++ coordLeft q :: q :: s) := by
    intro z hz
    induction hz with
    | nil =>
      intro p s q heq
      simp at heq
    | @cons x y hx hy ih =>
      intro p s q heq
      obtain ⟨t, hp, hy'⟩ | ⟨t, hx', hs⟩ := List.append_eq_append_iff.mp heq
      · subst p
        have htail := ih t s q hy'
        simpa [List.append_assoc] using CoordForest.cons hx htail
      · cases t with
        | nil =>
          simp only [List.append_nil] at hx' hs
          subst x
          have htail := ih [] s q (by simpa using hs.symm)
          simpa using CoordForest.cons hx htail
        | cons z t =>
          simp only [List.cons_append, List.cons.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          have hstep : CoordExpand x (p ++ coordLeft q :: q :: t) := by
            simpa [hx'] using CoordExpand.left p t q
          simpa [List.append_assoc] using
            CoordForest.cons (hx.tail hstep) hy
  have right_aux : ∀ (z : List EdgeCoord), CoordForest root z →
    ∀ (p s : List EdgeCoord) (q : EdgeCoord), z = p ++ q :: s →
      CoordForest root (p ++ q :: coordRight q :: s) := by
    intro z hz
    induction hz with
    | nil =>
      intro p s q heq
      simp at heq
    | @cons x y hx hy ih =>
      intro p s q heq
      obtain ⟨t, hp, hy'⟩ | ⟨t, hx', hs⟩ := List.append_eq_append_iff.mp heq
      · subst p
        have htail := ih t s q hy'
        simpa [List.append_assoc] using CoordForest.cons hx htail
      · cases t with
        | nil =>
          simp only [List.append_nil] at hx' hs
          subst x
          have htail := ih [] s q (by simpa using hs.symm)
          simpa using CoordForest.cons hx htail
        | cons z t =>
          simp only [List.cons_append, List.cons.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          have hstep : CoordExpand x (p ++ q :: coordRight q :: t) := by
            simpa [hx'] using CoordExpand.right p t q
          simpa [List.append_assoc] using
            CoordForest.cons (hx.tail hstep) hy
  cases h with
  | left p s q => exact left_aux _ hu p s q rfl
  | right p s q => exact right_aux _ hu p s q rfl

end OeisA108081

namespace OeisA108081

/--
[coordRootDecomp_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordRootDecomp_base
  {root : EdgeCoord} :
-- imply
  CoordRootDecomp root [root] :=
-- proof
⟨[], [], CoordForest.nil, CoordForest.nil, rfl⟩

end OeisA108081

namespace OeisA108081

/--
[CoordRootDecomp.expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordRootDecomp.expand
  {root : EdgeCoord}
  {u v : List EdgeCoord}
-- given
  (hu : CoordRootDecomp root u)
  (h : CoordExpand u v) :
-- imply
  CoordRootDecomp root v := by
-- proof
  cases h with
  | left p s q =>
    obtain ⟨L, R, hL, hR, heq⟩ := hu
    have hs := heq.symm
    obtain ⟨t, hp, htail⟩ | ⟨t, hL', hsuf⟩ := List.append_eq_append_iff.mp hs
    · cases t with
      | nil =>
        simp only [List.append_nil, List.nil_append, List.cons.injEq] at hp htail
        obtain ⟨rfl, rfl⟩ := htail
        refine ⟨L ++ [coordLeft root], R, hL.append (CoordForest.singleton _), hR, ?_⟩
        simp [hp, List.append_assoc]
      | cons z t =>
        simp only [List.cons_append, List.cons.injEq] at htail
        obtain ⟨rfl, hR'⟩ := htail
        have hstep : CoordExpand R (t ++ coordLeft q :: q :: s) := by
          simpa [hR'] using CoordExpand.left t s q
        refine ⟨L, t ++ coordLeft q :: q :: s, hL, hR.expand hstep, ?_⟩
        simp [hp, List.append_assoc]
    · cases t with
      | nil =>
        simp only [List.append_nil, List.nil_append, List.cons.injEq] at hL' hsuf
        obtain ⟨rfl, rfl⟩ := hsuf
        refine ⟨L ++ [coordLeft q], s, hL.append (CoordForest.singleton _), hR, ?_⟩
        simp [hL', List.append_assoc]
      | cons z t =>
        simp only [List.cons_append, List.cons.injEq] at hsuf
        obtain ⟨rfl, rfl⟩ := hsuf
        have hstep : CoordExpand L (p ++ coordLeft q :: q :: t) := by
          simpa [hL'] using CoordExpand.left p t q
        refine ⟨p ++ coordLeft q :: q :: t, R, hL.expand hstep, hR, ?_⟩
        simp [List.append_assoc]
  | right p s q =>
    obtain ⟨L, R, hL, hR, heq⟩ := hu
    have hs := heq.symm
    obtain ⟨t, hp, htail⟩ | ⟨t, hL', hsuf⟩ := List.append_eq_append_iff.mp hs
    · cases t with
      | nil =>
        simp only [List.append_nil, List.nil_append, List.cons.injEq] at hp htail
        obtain ⟨rfl, rfl⟩ := htail
        refine ⟨L, [coordRight root] ++ R, hL,
          (CoordForest.singleton _).append hR, ?_⟩
        simp [hp, List.append_assoc]
      | cons z t =>
        simp only [List.cons_append, List.cons.injEq] at htail
        obtain ⟨rfl, hR'⟩ := htail
        have hstep : CoordExpand R (t ++ q :: coordRight q :: s) := by
          simpa [hR'] using CoordExpand.right t s q
        refine ⟨L, t ++ q :: coordRight q :: s, hL, hR.expand hstep, ?_⟩
        simp [hp, List.append_assoc]
    · cases t with
      | nil =>
        simp only [List.append_nil, List.nil_append, List.cons.injEq] at hL' hsuf
        obtain ⟨rfl, rfl⟩ := hsuf
        refine ⟨L, [coordRight q] ++ s, hL,
          (CoordForest.singleton _).append hR, ?_⟩
        simp [hL', List.append_assoc]
      | cons z t =>
        simp only [List.cons_append, List.cons.injEq] at hsuf
        obtain ⟨rfl, rfl⟩ := hsuf
        have hstep : CoordExpand L (p ++ q :: coordRight q :: t) := by
          simpa [hL'] using CoordExpand.right p t q
        refine ⟨p ++ q :: coordRight q :: t, R, hL.expand hstep, hR, ?_⟩
        simp [List.append_assoc]

end OeisA108081

namespace OeisA108081

/--
[CoordTree.rootDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordTree.rootDecomp
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordTree root w) :
-- imply
  CoordRootDecomp root w := by
-- proof
  induction hw with
  | refl => exact coordRootDecomp_base root
  | tail _ h ih => exact ih.expand h

end OeisA108081

namespace OeisA108081

/--
[CoordExpand.head_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordExpand.head_fst
  {u v : List EdgeCoord}
-- given
  (h : CoordExpand u v) :
-- imply
  u.head?.map Prod.fst = v.head?.map Prod.fst := by
-- proof
  cases h with
  | left p s q => cases p <;> simp
  | right p s q => cases p <;> simp

end OeisA108081

namespace OeisA108081

/--
[CoordExpand.last_rightIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordExpand.last_rightIndex
  {u v : List EdgeCoord}
-- given
  (h : CoordExpand u v) :
-- imply
  u.getLast?.map rightIndex = v.getLast?.map rightIndex := by
-- proof
  cases h with
  | left p s q =>
    cases s with
    | nil => simp [rightIndex]
    | cons z s => simp [List.getLast?_append]
  | right p s q =>
    cases s with
    | nil => simp [rightIndex_coordRight]
    | cons z s => simp [List.getLast?_append]

end OeisA108081

namespace OeisA108081

/--
[CoordTree.head_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordTree.head_fst
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordTree root w) :
-- imply
  w.head?.map Prod.fst = some root.1 := by
-- proof
  have h : [root].head?.map Prod.fst = w.head?.map Prod.fst := by
    induction hw with
    | refl => rfl
    | tail _ hs ih => exact ih.trans hs.head_fst
  simpa using h.symm

end OeisA108081

namespace OeisA108081

/--
[CoordTree.last_rightIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordTree.last_rightIndex
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordTree root w) :
-- imply
  w.getLast?.map rightIndex = some (rightIndex root) := by
-- proof
  have h : [root].getLast?.map rightIndex = w.getLast?.map rightIndex := by
    induction hw with
    | refl => rfl
    | tail _ hs ih => exact ih.trans hs.last_rightIndex
  simpa using h.symm

end OeisA108081

namespace OeisA108081

/--
[CoordTree.path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordTree.path
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordTree root w) :
-- imply
  CoordPath w := by
-- proof
  induction hw with
  | refl => exact CoordPath.singleton _
  | tail _ h ih => exact ih.expand h

end OeisA108081

namespace OeisA108081

/--
[CoordTree.forestForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordTree.forestForm
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordTree root w) :
-- imply
  CoordForestForm root w :=
-- proof
Or.inr ⟨hw.path, hw.head_fst, hw.last_rightIndex⟩

end OeisA108081

namespace OeisA108081

/--
[CoordPath.append_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordPath.append_bridge
  {p s : List EdgeCoord}
  {q r : EdgeCoord}
-- given
  (hu : CoordPath (p ++ [q]))
  (hv : CoordPath (r :: s))
  (hqr : CoordAdjacent q r) :
-- imply
  CoordPath (p ++ q :: r :: s) := by
-- proof
  induction p with
  | nil =>
    simp only [List.nil_append] at hu ⊢
    exact CoordPath.cons hqr hv
  | cons x p ih =>
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons_append] at hu ⊢
      cases hu with
      | cons hxq _ => exact CoordPath.cons hxq (CoordPath.cons hqr hv)
    | cons y p =>
      simp only [List.cons_append] at hu ⊢
      cases hu with
      | cons hxy ht => exact CoordPath.cons hxy (ih ht)

end OeisA108081

namespace OeisA108081

/--
[CoordForest.nonempty_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForest.nonempty_form
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordForest root w)
  (hne : w ≠ []) :
-- imply
  CoordPath w ∧ w.head?.map Prod.fst = some root.1 ∧ w.getLast?.map rightIndex = some (rightIndex root) := by
-- proof
  induction hw with
  | nil => exact (hne rfl).elim
  | @cons u v hu hv ih =>
    by_cases hvnil : v = []
    · subst v
      simpa only [List.append_nil] using
        (⟨CoordTree.path hu, CoordTree.head_fst hu,
          CoordTree.last_rightIndex hu⟩ :
          CoordPath u ∧ u.head?.map Prod.fst = some root.1 ∧
            u.getLast?.map rightIndex = some (rightIndex root))
    · rcases ih hvnil with ⟨hvp, hvhead, hvlast⟩
      obtain hunil | ⟨p, q, hup⟩ := List.eq_nil_or_concat u
      · subst u
        have := CoordTree.head_fst hu
        simp at this
      · subst u
        cases v with
        | nil => contradiction
        | cons r s =>
          simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hvhead
          have hulast : rightIndex q = rightIndex root := by
            have ht := CoordTree.last_rightIndex hu
            simpa [List.concat_eq_append] using ht
          have hadj : CoordAdjacent q r := by
            obtain ⟨k, e⟩ := root
            cases e <;> simp [rightIndex, CoordAdjacent] at hulast hvhead ⊢ <;> omega
          have hupath : CoordPath (p ++ [q]) := by
            simpa [List.concat_eq_append] using CoordTree.path hu
          have hall := CoordPath.append_bridge hupath hvp hadj
          refine ⟨?_, ?_, ?_⟩
          · simpa [List.concat_eq_append] using hall
          · rw [List.concat_eq_append,
            List.head?_append_of_ne_nil (p ++ [q]) (by simp)]
            have ht := CoordTree.head_fst hu
            simpa [List.concat_eq_append] using ht
          · rw [List.getLast?_append_of_ne_nil _ (by simp : r :: s ≠ [])]
            exact hvlast

end OeisA108081

namespace OeisA108081

/--
[CoordForest.forestForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForest.forestForm
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordForest root w) :
-- imply
  CoordForestForm root w := by
-- proof
  by_cases h : w = []
  · exact Or.inl h
  · exact Or.inr (hw.nonempty_form h)

end OeisA108081

namespace OeisA108081

/--
[CoordExpand.with_context](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordExpand.with_context
  {u v : List EdgeCoord}
  {p s : List EdgeCoord}
-- given
  (h : CoordExpand u v) :
-- imply
  CoordExpand (p ++ u ++ s) (p ++ v ++ s) := by
-- proof
  cases h with
  | left q t z =>
    simpa only [List.append_assoc, List.cons_append] using
      CoordExpand.left (p ++ q) (t ++ s) z
  | right q t z =>
    simpa only [List.append_assoc, List.cons_append] using
      CoordExpand.right (p ++ q) (t ++ s) z

end OeisA108081

namespace OeisA108081

/--
[coordExpandStar_with_context](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordExpandStar_with_context
  {u v : List EdgeCoord}
  {p s : List EdgeCoord}
-- given
  (h : Relation.ReflTransGen CoordExpand u v) :
-- imply
  Relation.ReflTransGen CoordExpand (p ++ u ++ s) (p ++ v ++ s) :=
-- proof
  Relation.ReflTransGen.lift (fun w => p ++ w ++ s)
    (fun _ _ h' => h'.with_context p s) h

end OeisA108081

namespace OeisA108081

/--
[CoordForest.before_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForest.before_root
  {root : EdgeCoord}
  {L : List EdgeCoord}
  {p : List EdgeCoord}
-- given
  (hL : CoordForest (coordLeft root) L) :
-- imply
  Relation.ReflTransGen CoordExpand (p ++ [root]) (p ++ L ++ [root]) := by
-- proof
  induction hL generalizing p with
  | nil =>
    simpa using (Relation.ReflTransGen.refl :
      Relation.ReflTransGen CoordExpand (p ++ [root]) (p ++ [root]))
  | @cons u v hu hv ih =>
    have hleaf : CoordExpand (p ++ [root]) (p ++ [coordLeft root, root]) := by
      simpa using CoordExpand.left p [] root
    apply (Relation.ReflTransGen.single hleaf).trans
    have htree : Relation.ReflTransGen CoordExpand
      (p ++ [coordLeft root, root]) (p ++ u ++ [root]) := by
      simpa [List.append_assoc] using coordExpandStar_with_context hu p [root]
    exact htree.trans (by simpa [List.append_assoc] using ih (p ++ u))

end OeisA108081

namespace OeisA108081

/--
[CoordForest.after_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForest.after_root
  {root : EdgeCoord}
  {R : List EdgeCoord}
  {s : List EdgeCoord}
-- given
  (hR : CoordForest (coordRight root) R) :
-- imply
  Relation.ReflTransGen CoordExpand ([root] ++ s) ([root] ++ R ++ s) := by
-- proof
  induction hR generalizing s with
  | nil => exact Relation.ReflTransGen.refl
  | @cons u v hu hv ih =>
    have htail := ih s
    apply htail.trans
    have hleaf : CoordExpand ([root] ++ v ++ s)
      ([root, coordRight root] ++ v ++ s) := by
      simpa [List.append_assoc] using CoordExpand.right [] (v ++ s) root
    apply (Relation.ReflTransGen.single hleaf).trans
    simpa [List.append_assoc] using coordExpandStar_with_context hu [root] (v ++ s)

end OeisA108081

namespace OeisA108081

/--
[CoordRootDecomp.toTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordRootDecomp.toTree
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordRootDecomp root w) :
-- imply
  CoordTree root w := by
-- proof
  obtain ⟨L, R, hL, hR, rfl⟩ := hw
  have hl := hL.before_root []
  have hr := hR.after_root []
  apply hl.trans
  simpa [List.append_assoc] using coordExpandStar_with_context hr L []

end OeisA108081

namespace OeisA108081

/--
[coordTree_iff_rootDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordTree_iff_rootDecomp
  {root : EdgeCoord}
  {w : List EdgeCoord} :
-- imply
  CoordTree root w ↔ CoordRootDecomp root w :=
-- proof
  ⟨CoordTree.rootDecomp, CoordRootDecomp.toTree⟩

end OeisA108081

namespace OeisA108081

/--
[CoordInsert.rootDecomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordInsert.rootDecomp
  {w : List EdgeCoord}
-- given
  (hw : CoordInsert w) :
-- imply
  ∃ L R, CoordForest (0, true) L ∧ CoordForest (1, true) R ∧ w = L ++ (0, false) :: R := by
-- proof
  have ht : CoordTree (0, false) w := by simpa [CoordTree, CoordInsert] using hw
  obtain ⟨L, R, hL, hR, rfl⟩ := ht.rootDecomp
  exact ⟨L, R, by simpa [coordLeft] using hL, by simpa [coordRight] using hR, rfl⟩

end OeisA108081

namespace OeisA108081

/--
[coordInsert_iff_forest_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordInsert_iff_forest_decomp
  {w : List EdgeCoord} :
-- imply
  CoordInsert w ↔ ∃ L R, CoordForest (0, true) L ∧ CoordForest (1, true) R ∧ w = L ++ (0, false) :: R := by
-- proof
  constructor
  · exact CoordInsert.rootDecomp
  · rintro ⟨L, R, hL, hR, rfl⟩
    have hd : CoordRootDecomp (0, false) (L ++ (0, false) :: R) :=
      ⟨L, R, by simpa [coordLeft] using hL, by simpa [coordRight] using hR, rfl⟩
    simpa [CoordInsert, CoordTree] using hd.toTree

end OeisA108081

namespace OeisA108081

/--
[coordsToBits_append_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordsToBits_append_bridge
  {p s : List EdgeCoord}
  {q r : EdgeCoord} :
-- imply
  coordsToBits ((p ++ [q]) ++ r :: s) = coordsToBits (p ++ [q]) ++ [coordMovementBit q r] ++ coordsToBits (r :: s) := by
-- proof
  induction p with
  | nil => simp [coordsToBits]
  | cons x p ih =>
    cases p with
    | nil => simp [coordsToBits]
    | cons y p =>
      simp only [List.cons_append, coordsToBits, List.cons.injEq]
      refine ⟨trivial, trivial, ?_⟩
      convert ih using 1 <;> simp only [List.cons_append, List.append_assoc]

end OeisA108081

namespace OeisA108081

/--
[count_coordsToBits_of_root_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma count_coordsToBits_of_root_forest
  {root : EdgeCoord}
  {w : List EdgeCoord}
  {m : ℕ}
-- given
  (hw : CoordForest root w)
  (hlen : w.length = m + 1) :
-- imply
  (coordsToBits w).count true = m + if root.2 then 1 else 0 := by
-- proof
  have hne : w ≠ [] := by intro h; subst w; simp at hlen
  obtain ⟨hp, hhead, hlast⟩ := hw.nonempty_form hne
  have hbitlen : (coordsToBits w).length = 2 * m + 1 := by
    rw [length_coordsToBits hp, hlen]
    omega
  have hdecode := rightIndex_last_bitsToCoords root.1 m (coordsToBits w) hbitlen
  have hfirst : (w.head?.map Prod.fst).getD 0 = root.1 := by rw [hhead]; rfl
  have hdecode_eq : bitsToCoords root.1 (coordsToBits w) = w := by
    rw [← hfirst]
    exact bitsToCoords_coordsToBits hp
  rw [hdecode_eq, hlast] at hdecode
  obtain ⟨k, e⟩ := root
  cases e <;> simp [rightIndex] at hdecode ⊢ <;> omega

end OeisA108081

namespace OeisA108081

/--
[length_coordsToBits_of_root_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma length_coordsToBits_of_root_forest
  {root : EdgeCoord}
  {w : List EdgeCoord}
  {m : ℕ}
-- given
  (hw : CoordForest root w)
  (hlen : w.length = m + 1) :
-- imply
  (coordsToBits w).length = 2 * m + 1 := by
-- proof
  have hne : w ≠ [] := by intro h; subst w; simp at hlen
  rw [length_coordsToBits (hw.nonempty_form hne).1, hlen]
  omega

end OeisA108081

namespace OeisA108081

/--
[movement_from_left_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma movement_from_left_forest
  {L : List EdgeCoord}
  {q : EdgeCoord}
-- given
  (hL : CoordForest (0, true) L)
  (hne : L ≠ [])
  (hq : L.getLast? = some q) :
-- imply
  coordMovementBit q (0, false) = false := by
-- proof
  have hend := (hL.nonempty_form hne).2.2
  rw [hq] at hend
  obtain ⟨k, e⟩ := q
  cases e <;> simp [rightIndex, coordMovementBit] at hend ⊢ <;> omega

end OeisA108081

namespace OeisA108081

/--
[movement_to_right_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma movement_to_right_forest
  {R : List EdgeCoord}
  {q : EdgeCoord}
-- given
  (hR : CoordForest (1, true) R)
  (hne : R ≠ [])
  (hq : R.head? = some q) :
-- imply
  coordMovementBit (0, false) q = false := by
-- proof
  have hhead := (hR.nonempty_form hne).2.1
  rw [hq] at hhead
  obtain ⟨k, e⟩ := q
  cases e <;> simp [coordMovementBit] at hhead ⊢ <;> omega

end OeisA108081

namespace OeisA108081

/--
[balanced_pad_left_of_true_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma balanced_pad_left_of_true_forest
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hr : root.2 = true)
  (hw : CoordForest root w)
  (hne : w ≠ []) :
-- imply
  BitBalanced (false :: coordsToBits w) := by
-- proof
  have hpos : 0 < w.length := Nat.pos_of_ne_zero (by
    intro hz
    exact hne (List.length_eq_zero_iff.mp hz))
  let m := w.length - 1
  have hlen : w.length = m + 1 := by simp [m, Nat.sub_add_cancel (by omega : 1 ≤ w.length)]
  have hc := count_coordsToBits_of_root_forest hw hlen
  have hl := length_coordsToBits_of_root_forest hw hlen
  simp only [BitBalanced, List.count_cons, Bool.false_eq_true, ↓reduceIte,
    zero_add, List.length_cons]
  rw [hc, hl, hr]
  simp
  omega

end OeisA108081

namespace OeisA108081

/--
[balanced_pad_right_of_true_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma balanced_pad_right_of_true_forest
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hr : root.2 = true)
  (hw : CoordForest root w)
  (hne : w ≠ []) :
-- imply
  BitBalanced (coordsToBits w ++ [false]) := by
-- proof
  have h := balanced_pad_left_of_true_forest hr hw hne
  simpa [BitBalanced] using h

end OeisA108081

namespace OeisA108081

/--
[bitBalanced_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitBalanced_append
  {u v : List Bool}
-- given
  (hu : BitBalanced u)
  (hv : BitBalanced v) :
-- imply
  BitBalanced (u ++ v) := by
-- proof
  unfold BitBalanced at hu hv ⊢
  rw [List.count_append, List.length_append]
  omega

end OeisA108081

namespace OeisA108081

/--
[bitBalanced_count_false_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitBalanced_count_false_eq
  {p : List Bool}
-- given
  (hp : BitBalanced p) :
-- imply
  p.count false = p.count true := by
-- proof
  unfold BitBalanced at hp
  have ht := List.count_true_add_count_false p
  omega

end OeisA108081

namespace OeisA108081

/--
[bitBalanced_three_false_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitBalanced_three_false_prefix
  {p s : List Bool}
-- given
  (hp : BitBalanced p)
  (hs : BitBalanced s) :
-- imply
  (false :: p ++ [false, false] ++ s).count true + 3 = (false :: p ++ [false, false] ++ s).count false := by
-- proof
  have hp0 := bitBalanced_count_false_eq hp
  have hs0 := bitBalanced_count_false_eq hs
  simp [List.count_append, hp0, hs0]
  omega

end OeisA108081

namespace OeisA108081

/--
[crossingFree_of_shortest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma crossingFree_of_shortest
  {E p s : List Bool}
-- given
  (hcross : E = p ++ [false, false, false] ++ s)
  (hbal : BitBalanced p)
  (hmin : ∀ q t, E = q ++ [false, false, false] ++ t → BitBalanced q → p.length ≤ q.length) :
-- imply
  CrossingFree p := by
-- proof
  intro q t hpq hq
  have hE : E = q ++ [false, false, false] ++
    (t ++ [false, false, false] ++ s) := by
    rw [hcross, hpq]
    simp [List.append_assoc]
  have hlen := hmin q (t ++ [false, false, false] ++ s) hE hq
  have hstrict : q.length < p.length := by
    have he := congrArg List.length hpq
    simp only [List.length_append, List.length_cons, List.length_nil] at he
    omega
  omega

end OeisA108081

namespace OeisA108081

/--
[exists_crossingFree_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma exists_crossingFree_split
  {E : List Bool}
-- given
  (h : ∃ p s, E = p ++ [false, false, false] ++ s ∧ BitBalanced p) :
-- imply
  ∃ p s, E = p ++ [false, false, false] ++ s ∧ BitBalanced p ∧ CrossingFree p := by
-- proof
  classical
  let P : ℕ → Prop := fun n => ∃ p s, p.length = n ∧
    E = p ++ [false, false, false] ++ s ∧ BitBalanced p
  have hP : ∃ n, P n := by
    obtain ⟨p, s, he, hp⟩ := h
    exact ⟨p.length, p, s, rfl, he, hp⟩
  obtain ⟨p, s, hlen, he, hp⟩ := Nat.find_spec hP
  refine ⟨p, s, he, hp, crossingFree_of_shortest he hp ?_⟩
  intro q t hqt hq
  have hPQ : P q.length := ⟨q, t, rfl, hqt, hq⟩
  have hleast := Nat.find_min' hP hPQ
  omega

end OeisA108081

namespace OeisA108081

/--
[exists_firstCrossingPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma exists_firstCrossingPrefix
  {E : List Bool}
-- given
  (h : ∃ p s, E = p ++ [false, false, false] ++ s ∧ BitBalanced p) :
-- imply
  ∃ p, FirstCrossingPrefix E p := by
-- proof
  classical
  let P : ℕ → Prop := fun n => ∃ p s, p.length = n ∧
    E = p ++ [false, false, false] ++ s ∧ BitBalanced p
  have hP : ∃ n, P n := by
    obtain ⟨p, s, he, hp⟩ := h
    exact ⟨p.length, p, s, rfl, he, hp⟩
  obtain ⟨p, s, hlen, he, hp⟩ := Nat.find_spec hP
  refine ⟨p, hp, ⟨s, he⟩, ?_⟩
  intro q t hqt hq
  have hPQ : P q.length := ⟨q, t, rfl, hqt, hq⟩
  have hleast := Nat.find_min' hP hPQ
  omega

end OeisA108081

namespace OeisA108081

/--
[firstCrossingPrefix_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma firstCrossingPrefix_unique
  {E p q : List Bool}
-- given
  (hp : FirstCrossingPrefix E p)
  (hq : FirstCrossingPrefix E q) :
-- imply
  p = q := by
-- proof
  obtain ⟨s, hs⟩ := hp.2.1
  obtain ⟨t, ht⟩ := hq.2.1
  have hpq := hp.2.2 q t ht hq.1
  have hqp := hq.2.2 p s hs hp.1
  have hlen : p.length = q.length := by omega
  have hpref : E.take p.length = p := by rw [hs]; simp
  have hqref : E.take q.length = q := by rw [ht]; simp
  rw [← hpref, hlen, hqref]

end OeisA108081

namespace OeisA108081

/--
[bitBalanced_even_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma bitBalanced_even_length
  {p : List Bool}
-- given
  (hp : BitBalanced p) :
-- imply
  Even p.length :=
-- proof
⟨p.count true, by simpa [BitBalanced, two_mul] using hp.symm⟩

end OeisA108081

namespace OeisA108081

/--
[balanced_prefix_starts_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma balanced_prefix_starts_false
  {b p s : List Bool}
-- given
  (he : false :: b ++ [false] = p ++ [false, false, false] ++ s) :
-- imply
  p = [] ∨ p.head? = some false := by
-- proof
  cases p with
  | nil => exact Or.inl rfl
  | cons x xs =>
    right
    have hh := congrArg List.head? he
    simpa using hh

end OeisA108081

namespace OeisA108081

/--
[balanced_suffix_ends_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma balanced_suffix_ends_false
  {b p s : List Bool}
-- given
  (he : false :: b ++ [false] = p ++ [false, false, false] ++ s) :
-- imply
  s = [] ∨ s.getLast? = some false := by
-- proof
  cases s with
  | nil => exact Or.inl rfl
  | cons x xs =>
    right
    have hh := congrArg List.getLast? he
    rw [List.getLast?_append_of_ne_nil
      (p ++ [false, false, false]) (by simp : x :: xs ≠ [])] at hh
    apply hh.symm.trans
    exact List.getLast?_concat

end OeisA108081

namespace OeisA108081

/--
[centered_split_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma centered_split_length
  {m : ℕ}
  {b p s : List Bool}
-- given
  (hb : b ∈ ForestBits m)
  (he : false :: b ++ [false] = p ++ [false, false, false] ++ s) :
-- imply
  p.length + s.length = 2 * m := by
-- proof
  rw [ForestBits, Set.mem_setOf_eq] at hb
  have hl := congrArg List.length he
  simp only [List.length_cons, List.length_append, List.length_nil] at hl
  omega

end OeisA108081

namespace OeisA108081

/--
[suffix_balanced_of_forest_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma suffix_balanced_of_forest_crossing
  {m : ℕ}
  {b p s : List Bool}
-- given
  (hb : b ∈ ForestBits m)
  (he : false :: b ++ [false] = p ++ [false, false, false] ++ s)
  (hp : BitBalanced p) :
-- imply
  BitBalanced s := by
-- proof
  rw [ForestBits, Set.mem_setOf_eq] at hb
  unfold BitBalanced at hp ⊢
  have hl := congrArg List.length he
  have hc := congrArg (List.count true) he
  simp only [List.length_cons, List.length_append, List.length_nil,
    List.count_cons, List.count_append, List.count_nil] at hl hc
  simp at hc
  omega

end OeisA108081

namespace OeisA108081

/--
[centered_exists_first_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma centered_exists_first_split
  {m : ℕ}
  {b : List Bool}
-- given
  (hb : b ∈ CenteredTreeBits m) :
-- imply
  ∃ p s, false :: b ++ [false] = p ++ [false, false, false] ++ s ∧ BitBalanced p ∧ BitBalanced s ∧ FirstCrossingPrefix (false :: b ++ [false]) p := by
-- proof
  rw [CenteredTreeBits, Set.mem_setOf_eq] at hb
  obtain ⟨hfb, p, s, he, hp, hs⟩ := hb
  rcases exists_firstCrossingPrefix
    (E := false :: b ++ [false]) ⟨p, s, he, hp⟩ with ⟨q, hq⟩
  obtain ⟨t, ht⟩ := hq.2.1
  refine ⟨q, t, ht, hq.1, ?_, hq⟩
  exact suffix_balanced_of_forest_crossing hfb ht hq.1

end OeisA108081

namespace OeisA108081

/--
[cons_stripEnds_concat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma cons_stripEnds_concat
  {E : List Bool}
-- given
  (hlen : 2 ≤ E.length)
  (hf : E.head? = some false)
  (hl : E.getLast? = some false) :
-- imply
  false :: stripEnds E ++ [false] = E := by
-- proof
  cases E with
  | nil => simp at hlen
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at hf
    subst x
    obtain rfl | ⟨u, y, rfl⟩ := List.eq_nil_or_concat xs
    · simp at hlen
    · simp only [stripEnds, List.tail_cons, List.dropLast_concat]
      have htail : (u ++ [y]).getLast? = some false := by
        have hlast : (false :: (u ++ [y])).getLast? = some false := by
          simpa [List.concat_eq_append] using hl
        rwa [List.getLast?_cons_of_ne_nil (by simp : u ++ [y] ≠ [])] at hlast
      have hy : y = false := by simpa using htail
      subst y
      simp

end OeisA108081

namespace OeisA108081

/--
[centered_has_canonicalPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma centered_has_canonicalPair
  {m : ℕ}
  {b : List Bool}
-- given
  (hb : b ∈ CenteredTreeBits m) :
-- imply
  ∃ ps ∈ CanonicalPairs m, canonicalGlue ps = b := by
-- proof
  obtain ⟨p, s, he, hp, hs, hfirst⟩ := centered_exists_first_split hb
  refine ⟨(p, s), ?_, ?_⟩
  · rw [CanonicalPairs, Set.mem_setOf_eq]
    change BitBalanced p ∧ BitBalanced s ∧ p.length + s.length = 2 * m ∧
      (p = [] ∨ p.head? = some false) ∧
      (s = [] ∨ s.getLast? = some false) ∧
      FirstCrossingPrefix (p ++ [false, false, false] ++ s) p
    have hfb : b ∈ ForestBits m := by
      rwa [CenteredTreeBits, Set.mem_setOf_eq] at hb
    exact ⟨hp, hs, centered_split_length hfb he,
      balanced_prefix_starts_false he, balanced_suffix_ends_false he,
      by simpa [he] using hfirst⟩
  · have houter : false :: canonicalGlue (p, s) ++ [false] =
    false :: b ++ [false] := by
    calc
      false :: canonicalGlue (p, s) ++ [false] =
        p ++ [false, false, false] ++ s := by
        apply cons_stripEnds_concat
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · rw [← he]
          rfl
        · rw [← he]
          exact List.getLast?_concat
      _ = false :: b ++ [false] := he.symm
    have htail := (List.cons.inj houter).2
    exact List.append_cancel_right htail

end OeisA108081

namespace OeisA108081

/--
[canonicalPair_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma canonicalPair_outer
  {m : ℕ}
  {p s : List Bool}
-- given
  (hps : (p, s) ∈ CanonicalPairs m) :
-- imply
  false :: canonicalGlue (p, s) ++ [false] = p ++ [false, false, false] ++ s := by
-- proof
  rw [CanonicalPairs, Set.mem_setOf_eq] at hps
  change BitBalanced p ∧ BitBalanced s ∧ p.length + s.length = 2 * m ∧
    (p = [] ∨ p.head? = some false) ∧
    (s = [] ∨ s.getLast? = some false) ∧
    FirstCrossingPrefix (p ++ [false, false, false] ++ s) p at hps
  apply cons_stripEnds_concat (E := p ++ [false, false, false] ++ s)
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rcases hps.2.2.2.1 with hp | hp
    · subst p
      rfl
    · cases p with
      | nil => simp at hp
      | cons x xs => simpa using hp
  · rcases hps.2.2.2.2.1 with hs | hs
    · subst s
      simp
    · cases s with
      | nil => simp at hs
      | cons x xs => simpa using hs

end OeisA108081

namespace OeisA108081

/--
[canonicalGlue_mem_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma canonicalGlue_mem_centered
  {m : ℕ}
  {p s : List Bool}
-- given
  (hps : (p, s) ∈ CanonicalPairs m) :
-- imply
  canonicalGlue (p, s) ∈ CenteredTreeBits m := by
-- proof
  rw [CanonicalPairs, Set.mem_setOf_eq] at hps
  change BitBalanced p ∧ BitBalanced s ∧ p.length + s.length = 2 * m ∧
    (p = [] ∨ p.head? = some false) ∧
    (s = [] ∨ s.getLast? = some false) ∧
    FirstCrossingPrefix (p ++ [false, false, false] ++ s) p at hps
  rw [CenteredTreeBits, Set.mem_setOf_eq]
  have hout := canonicalPair_outer (p := p) (s := s) (by
    rw [CanonicalPairs, Set.mem_setOf_eq]
    exact hps)
  refine ⟨?_, p, s, hout, hps.1, hps.2.1⟩
  rw [ForestBits, Set.mem_setOf_eq]
  constructor
  · have hl := congrArg List.length hout
    simp only [List.length_cons, List.length_append, List.length_nil] at hl
    omega
  · have hc := congrArg (List.count true) hout
    have hp := hps.1
    have hs := hps.2.1
    unfold BitBalanced at hp hs
    simp only [List.count_cons, List.count_append, List.count_nil] at hc
    simp at hc
    omega

end OeisA108081

namespace OeisA108081

/--
[canonicalGlue_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma canonicalGlue_injOn
  {m : ℕ} :
-- imply
  Set.InjOn canonicalGlue (CanonicalPairs m) := by
-- proof
  rintro ⟨p, s⟩ hp ⟨q, t⟩ hq heq
  have hop := canonicalPair_outer hp
  have hoq := canonicalPair_outer hq
  have houter : p ++ [false, false, false] ++ s =
    q ++ [false, false, false] ++ t := by
    rw [← hop, ← hoq, heq]
  rw [CanonicalPairs, Set.mem_setOf_eq] at hp hq
  have hfirstp := hp.2.2.2.2.2
  have hfirstq := hq.2.2.2.2.2
  have hpq : p = q := firstCrossingPrefix_unique hfirstp (by
    simpa [houter] using hfirstq)
  subst q
  have hs : s = t := by
    exact List.append_cancel_left houter
  subst t
  rfl

end OeisA108081

namespace OeisA108081

/--
[image_canonicalGlue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma image_canonicalGlue
  {m : ℕ} :
-- imply
  canonicalGlue '' CanonicalPairs m = CenteredTreeBits m := by
-- proof
  ext b
  constructor
  · rintro ⟨ps, hps, rfl⟩
    obtain ⟨p, s⟩ := ps
    exact canonicalGlue_mem_centered hps
  · intro hb
    obtain ⟨ps, hps, rfl⟩ := centered_has_canonicalPair hb
    exact ⟨ps, hps, rfl⟩

end OeisA108081

namespace OeisA108081

/--
[ncard_centeredTreeBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_centeredTreeBits
  {m : ℕ} :
-- imply
  (CenteredTreeBits m).ncard = (CanonicalPairs m).ncard := by
-- proof
  rw [← image_canonicalGlue]
  exact Set.ncard_image_of_injOn (canonicalGlue_injOn m)

end OeisA108081

namespace OeisA108081

/--
[firstCrossingPrefix_iff_crossingFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma firstCrossingPrefix_iff_crossingFree
  {p s : List Bool} :
-- imply
  FirstCrossingPrefix (p ++ [false, false, false] ++ s) p ↔ BitBalanced p ∧ CrossingFree p := by
-- proof
  constructor
  · intro h
    exact ⟨h.1, crossingFree_of_shortest rfl h.1 h.2.2⟩
  · rintro ⟨hp, hfree⟩
    refine ⟨hp, ⟨s, rfl⟩, ?_⟩
    intro q t hqt hq
    by_contra hlen
    have hlt : q.length < p.length := by omega
    have heq : p ++ ([false, false, false] ++ s) =
      q ++ ([false, false, false] ++ t) := by
      simpa [List.append_assoc] using hqt
    rcases List.append_eq_append_iff.mp heq with
      ⟨u, hqp, htail⟩ | ⟨u, hpq, htail⟩
    · have hlength := congrArg List.length hqp
      simp only [List.length_append] at hlength
      omega
    · have hu_bal : BitBalanced u := by
      unfold BitBalanced at hp hq ⊢
      rw [hpq, List.count_append, List.length_append] at hp
      omega
      cases u with
      | nil =>
        simp at hpq
        subst q
        omega
      | cons x u =>
        cases u with
        | nil =>
          unfold BitBalanced at hu_bal
          simp at hu_bal
        | cons y u =>
          cases u with
          | nil =>
            simp only [List.cons_append, List.cons.injEq] at htail
            obtain ⟨rfl, rfl, htail⟩ := htail
            unfold BitBalanced at hu_bal
            simp at hu_bal
          | cons z u =>
            simp only [List.cons_append, List.cons.injEq] at htail
            obtain ⟨rfl, rfl, rfl, htail⟩ := htail
            exact hfree q u (by simpa [List.append_assoc] using hpq) hq

end OeisA108081

namespace OeisA108081

/--
[canonicalPair_iff_crossingFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma canonicalPair_iff_crossingFree
  {m : ℕ}
  {p s : List Bool} :
-- imply
  (p, s) ∈ CanonicalPairs m ↔ BitBalanced p ∧ BitBalanced s ∧ p.length + s.length = 2 * m ∧ (p = [] ∨ p.head? = some false) ∧ (s = [] ∨ s.getLast? = some false) ∧ CrossingFree p := by
-- proof
  rw [CanonicalPairs, Set.mem_setOf_eq]
  change (BitBalanced p ∧ BitBalanced s ∧ p.length + s.length = 2 * m ∧
    (p = [] ∨ p.head? = some false) ∧
    (s = [] ∨ s.getLast? = some false) ∧
    FirstCrossingPrefix (p ++ [false, false, false] ++ s) p) ↔ _
  rw [firstCrossingPrefix_iff_crossingFree]
  aesop

end OeisA108081

namespace OeisA108081

/--
[image_subsetBits_powersetCard_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma image_subsetBits_powersetCard_general
  {N K : ℕ} :
-- imply
  subsetBits N '' (↑((Finset.univ : Finset (Fin N)).powersetCard K) : Set (Finset (Fin N))) = WeightBits N K := by
-- proof
  ext b
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [WeightBits, Set.mem_setOf_eq]
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hu
    exact ⟨length_subsetBits _ _, by rw [count_subsetBits, hu.2]⟩
  · intro hb
    rw [WeightBits, Set.mem_setOf_eq] at hb
    let v : List.Vector Bool N := ⟨b, hb.1⟩
    let u : Finset (Fin N) := {i | v.get i = true}
    have hucard : u.card = K := by
      rwa [Fin.card_filter_univ_eq_vector_get_eq_count true v]
    refine ⟨u, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hucard⟩
    · have hf : (fun i : Fin N => decide (i ∈ u)) =
      fun i => v.get i := by
      funext i
      simp [u]
      rw [subsetBits, hf]
      calc
        List.ofFn (fun i => v.get i) =
          (List.Vector.ofFn (fun i => v.get i)).toList :=
          (List.Vector.toList_ofFn _).symm
        _ = v.toList := congrArg List.Vector.toList (List.Vector.ofFn_get v)
        _ = b := rfl

end OeisA108081

namespace OeisA108081

/--
[ncard_weightBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_weightBits
  {N K : ℕ} :
-- imply
  (WeightBits N K).ncard = N.choose K := by
-- proof
  rw [← image_subsetBits_powersetCard_general]
  rw [Set.ncard_image_of_injective _ (subsetBits_injective _)]
  simp [Set.ncard_coe_finset, Finset.card_powersetCard]

end OeisA108081

namespace OeisA108081

/--
[image_append_false_weightBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma image_append_false_weightBits
  {k : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  (fun b : List Bool => b ++ [false]) '' WeightBits (2 * k - 1) k = SuffixBits k := by
-- proof
  ext s
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [WeightBits, Set.mem_setOf_eq] at hb
    rw [SuffixBits, Set.mem_setOf_eq]
    refine ⟨?_, ?_, Or.inr List.getLast?_concat⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · unfold BitBalanced
      norm_num [List.length_append] at *
      omega
  · intro hs
    rw [SuffixBits, Set.mem_setOf_eq] at hs
    obtain rfl | ⟨b, y, rfl⟩ := List.eq_nil_or_concat s
    · have hk0 : k = 0 := by simpa using hs.1
      exact (Nat.ne_of_gt hk hk0).elim
    · have hy : y = false := by
      obtain h | h := hs.2.2
      · rw [List.concat_eq_append] at h
        exact (List.concat_ne_nil y b h).elim
      · rw [List.concat_eq_append, List.getLast?_concat] at h
        exact Option.some.inj h
      subst y
      refine ⟨b, ?_, by simp [List.concat_eq_append]⟩
      rw [WeightBits, Set.mem_setOf_eq]
      constructor
      · rw [List.concat_eq_append] at hs
        norm_num [List.length_append] at hs
        omega
      · unfold BitBalanced at hs
        rw [List.concat_eq_append] at hs
        norm_num [List.length_append] at hs
        omega

end OeisA108081

namespace OeisA108081

/--
[append_false_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma append_false_injective
-- imply
  Function.Injective (fun b : List Bool => b ++ [false]) := by
-- proof
  intro b c h
  exact List.append_cancel_right h

end OeisA108081

namespace OeisA108081

/--
[ncard_suffixBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_suffixBits
  {k : ℕ} :
-- imply
  (SuffixBits k).ncard = (2 * k - 1).choose k := by
-- proof
  cases k with
  | zero =>
    have hset : SuffixBits 0 = {[]} := by
      ext s
      constructor
      · intro hs
        rw [SuffixBits, Set.mem_setOf_eq] at hs
        have hnil : s = [] := List.length_eq_zero_iff.mp (by
          simpa using hs.1)
        simpa [hnil]
      · intro hs
        have hnil : s = [] := by simpa using hs
        subst s
        simp [SuffixBits, BitBalanced]
    rw [hset]
    simp
  | succ k =>
    rw [← image_append_false_weightBits (k + 1) (by omega)]
    rw [Set.ncard_image_of_injective _ append_false_injective]
    exact ncard_weightBits _ _

end OeisA108081

namespace OeisA108081

/--
[reverse_mem_suffixBits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma reverse_mem_suffixBits_iff
  {j : ℕ}
  {p : List Bool} :
-- imply
  p.reverse ∈ SuffixBits j ↔ p ∈ AllPrefixBits j := by
-- proof
  simp [SuffixBits, AllPrefixBits, BitBalanced]

end OeisA108081

namespace OeisA108081

/--
[image_reverse_allPrefixBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma image_reverse_allPrefixBits
  {j : ℕ} :
-- imply
  List.reverse '' AllPrefixBits j = SuffixBits j := by
-- proof
  ext s
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact reverse_mem_suffixBits_iff.mpr hp
  · intro hs
    refine ⟨s.reverse, ?_, by simp⟩
    rw [← reverse_mem_suffixBits_iff]
    simpa using hs

end OeisA108081

namespace OeisA108081

/--
[ncard_allPrefixBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_allPrefixBits
  {j : ℕ} :
-- imply
  (AllPrefixBits j).ncard = (2 * j - 1).choose j := by
-- proof
  calc
    (AllPrefixBits j).ncard = (List.reverse '' AllPrefixBits j).ncard :=
      (Set.ncard_image_of_injective _ List.reverse_injective).symm
    _ = (SuffixBits j).ncard := by rw [image_reverse_allPrefixBits]
    _ = (2 * j - 1).choose j := ncard_suffixBits j

end OeisA108081

namespace OeisA108081

/--
[prefixBits_subset_allPrefixBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma prefixBits_subset_allPrefixBits
  {j : ℕ} :
-- imply
  PrefixBits j ⊆ AllPrefixBits j := by
-- proof
  intro p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

end OeisA108081

namespace OeisA108081

/--
[allPrefixBits_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma allPrefixBits_finite
  {j : ℕ} :
-- imply
  (AllPrefixBits j).Finite := by
-- proof
  apply (List.finite_length_eq Bool (2 * j)).subset
  intro p hp
  exact hp.1

end OeisA108081

namespace OeisA108081

/--
[image_badGlue_badPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma image_badGlue_badPairs
  {j : ℕ} :
-- imply
  badGlue '' BadPairs j = AllPrefixBits j \ PrefixBits j := by
-- proof
  classical
  ext p
  constructor
  · rintro ⟨⟨q, t⟩, hqt, rfl⟩
    rw [BadPairs, Set.mem_iUnion] at hqt
    obtain ⟨r, hq, ht, hge⟩ := hqt
    change q ∈ PrefixBits (r : ℕ) at hq
    change t ∈ WeightBits (2 * (j - (r : ℕ)) - 3) (j - (r : ℕ)) at ht
    rw [PrefixBits, Set.mem_setOf_eq] at hq
    rw [WeightBits, Set.mem_setOf_eq] at ht
    change (q ++ [false, false, false] ++ t) ∈
      AllPrefixBits j \ PrefixBits j
    rw [Set.mem_diff]
    constructor
    · rw [AllPrefixBits, Set.mem_setOf_eq]
      have hrle : (r : ℕ) ≤ j := by omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · unfold BitBalanced at hq ⊢
        simp only [List.count_append, List.count_cons, List.count_nil]
        simp
        omega
      · have hhead := hq.2.2.1
        cases q with
        | nil => simp
        | cons x xs =>
          right
          simp only [List.cons_append, List.head?_cons] at hhead ⊢
          obtain hnil | hhead := hhead
          · simp at hnil
          · exact hhead
    · intro hmem
      rw [PrefixBits, Set.mem_setOf_eq] at hmem
      exact hmem.2.2.2 q t rfl hq.2.1
  · intro hp
    rw [Set.mem_diff, AllPrefixBits, Set.mem_setOf_eq] at hp
    obtain ⟨⟨hlen, hbal, hhead⟩, hnpre⟩ := hp
    have hnfree : ¬ CrossingFree p := by
      intro hfree
      apply hnpre
      exact ⟨hlen, hbal, hhead, hfree⟩
    rw [CrossingFree] at hnfree
    push_neg at hnfree
    obtain ⟨q, t, he, hq⟩ := hnfree
    rcases exists_crossingFree_split (E := p) ⟨q, t, he, hq⟩ with
      ⟨q, t, he, hq, hqfree⟩
    let r := q.count true
    have hqlen : q.length = 2 * r := by
      unfold BitBalanced at hq
      omega
    have hrle : r ≤ j := by
      have hl := congrArg List.length he
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      omega
    refine ⟨(q, t), ?_, by simpa [badGlue] using he.symm⟩
    rw [BadPairs, Set.mem_iUnion]
    refine ⟨⟨r, by omega⟩, ?_⟩
    change q ∈ PrefixBits r ∧
      t ∈ WeightBits (2 * (j - r) - 3) (j - r) ∧ 3 ≤ j - r
    have hl := congrArg List.length he
    have hc := congrArg (List.count true) he
    have hct := (List.count_le_length (a := true) (l := t))
    unfold BitBalanced at hbal
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.count_append, List.count_cons, List.count_nil] at hl hc
    simp at hc
    have hge : 3 ≤ j - r := by omega
    refine ⟨?_, ?_, hge⟩
    · rw [PrefixBits, Set.mem_setOf_eq]
      refine ⟨hqlen, hq, ?_, hqfree⟩
      cases q with
      | nil => simp
      | cons x xs =>
        right
        obtain hpnil | hph := hhead
        · rw [hpnil] at he
          simp at he
        · have hh := congrArg List.head? he
          simp only [List.cons_append, List.head?_cons] at hh ⊢
          exact hh.symm.trans hph
    · rw [WeightBits, Set.mem_setOf_eq]
      constructor <;> omega

end OeisA108081

namespace OeisA108081

/--
[badGlue_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma badGlue_injOn
  {j : ℕ} :
-- imply
  Set.InjOn badGlue (BadPairs j) := by
-- proof
  rintro ⟨q, t⟩ hqt ⟨q', t'⟩ hqt' heq
  rw [BadPairs, Set.mem_iUnion] at hqt hqt'
  obtain ⟨r, hq, ht, hge⟩ := hqt
  obtain ⟨r', hq', ht', hge'⟩ := hqt'
  change q ∈ PrefixBits (r : ℕ) at hq
  change q' ∈ PrefixBits (r' : ℕ) at hq'
  have hfirst : FirstCrossingPrefix (q ++ [false, false, false] ++ t) q :=
    firstCrossingPrefix_iff_crossingFree.mpr ⟨hq.2.1, hq.2.2.2⟩
  have hfirst' : FirstCrossingPrefix (q' ++ [false, false, false] ++ t') q' :=
    firstCrossingPrefix_iff_crossingFree.mpr ⟨hq'.2.1, hq'.2.2.2⟩
  unfold badGlue at heq
  have hqq : q = q' := firstCrossingPrefix_unique hfirst (by
    simpa [heq] using hfirst')
  subst q'
  have htt : t = t' := List.append_cancel_left heq
  subst t'
  rfl

end OeisA108081

namespace OeisA108081

/--
[badPairs_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma badPairs_finite
  {j : ℕ} :
-- imply
  (BadPairs j).Finite := by
-- proof
  rw [BadPairs]
  apply Set.finite_iUnion
  intro r
  apply ((List.finite_length_eq Bool (2 * (r : ℕ))).prod
    (List.finite_length_eq Bool (2 * (j - (r : ℕ)) - 3))).subset
  rintro ⟨q, t⟩ h
  exact ⟨h.1.1, h.2.1.1⟩

end OeisA108081

namespace OeisA108081

/--
[ncard_badPart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_badPart
  {j : ℕ} :
-- imply
  (AllPrefixBits j \ PrefixBits j).ncard = (BadPairs j).ncard := by
-- proof
  rw [← image_badGlue_badPairs]
  exact Set.ncard_image_of_injOn (badGlue_injOn j)

end OeisA108081

namespace OeisA108081

/--
[prefix_bad_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma prefix_bad_partition
  {j : ℕ} :
-- imply
  AllPrefixBits j = PrefixBits j ∪ (AllPrefixBits j \ PrefixBits j) :=
-- proof
(Set.union_diff_cancel (prefixBits_subset_allPrefixBits j)).symm

end OeisA108081

namespace OeisA108081

/--
[ncard_allPrefix_eq_prefix_add_bad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_allPrefix_eq_prefix_add_bad
  {j : ℕ} :
-- imply
  (AllPrefixBits j).ncard = (PrefixBits j).ncard + (BadPairs j).ncard := by
-- proof
  have hpfin : (PrefixBits j).Finite :=
    (allPrefixBits_finite j).subset (prefixBits_subset_allPrefixBits j)
  have hdfin : (AllPrefixBits j \ PrefixBits j).Finite :=
    (allPrefixBits_finite j).sdiff
  rw [prefix_bad_partition]
  rw [Set.ncard_union_eq Set.disjoint_sdiff_right hpfin hdfin]
  rw [ncard_badPart]

end OeisA108081

namespace OeisA108081

/--
[prefixBits_finite_early](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma prefixBits_finite_early
  {j : ℕ} :
-- imply
  (PrefixBits j).Finite := by
-- proof
  apply (List.finite_length_eq Bool (2 * j)).subset
  intro p hp
  exact hp.1

end OeisA108081

namespace OeisA108081

/--
[badPairs_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma badPairs_disjoint
  {j : ℕ} :
-- imply
  Pairwise (Function.onFun Disjoint (fun r : Fin (j + 1) => {qt : List Bool × List Bool | qt.1 ∈ PrefixBits r ∧ qt.2 ∈ WeightBits (2 * (j - r) - 3) (j - r) ∧ 3 ≤ j - r})) := by
-- proof
  intro r s hrs
  change Disjoint
    {qt : List Bool × List Bool | qt.1 ∈ PrefixBits r ∧
      qt.2 ∈ WeightBits (2 * (j - r) - 3) (j - r) ∧ 3 ≤ j - r}
    {qt : List Bool × List Bool | qt.1 ∈ PrefixBits s ∧
      qt.2 ∈ WeightBits (2 * (j - s) - 3) (j - s) ∧ 3 ≤ j - s}
  rw [Set.disjoint_left]
  rintro ⟨q, t⟩ hqr hqs
  exfalso
  apply hrs
  apply Fin.ext
  have hrlen := hqr.1.1
  have hslen := hqs.1.1
  omega

end OeisA108081

namespace OeisA108081

/--
[ncard_badPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_badPairs
  {j : ℕ} :
-- imply
  (BadPairs j).ncard = ∑ r : Fin (j + 1), if 3 ≤ j - (r : ℕ) then (PrefixBits r).ncard * (2 * (j - r) - 3).choose (j - r) else 0 := by
-- proof
  rw [BadPairs]
  have hu := Set.ncard_iUnion_of_finite
    (ι := Fin (j + 1))
    (s := fun r : Fin (j + 1) =>
      {qt : List Bool × List Bool | qt.1 ∈ PrefixBits r ∧
        qt.2 ∈ WeightBits (2 * (j - r) - 3) (j - r) ∧ 3 ≤ j - r})
    (fun r => ((prefixBits_finite_early r).prod
      ((List.finite_length_eq Bool (2 * (j - r) - 3)).subset
        (fun t ht => ht.1))).subset (fun qt h => ⟨h.1, h.2.1⟩))
    (badPairs_disjoint j)
  rw [hu, finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : 3 ≤ j - (r : ℕ)
  · rw [if_pos h]
    have heq : {qt : List Bool × List Bool |
      qt.1 ∈ PrefixBits r ∧
        qt.2 ∈ WeightBits (2 * (j - r) - 3) (j - r) ∧ 3 ≤ j - r} =
      PrefixBits r ×ˢ WeightBits (2 * (j - r) - 3) (j - r) := by
      ext qt
      simp [h]
    rw [heq, Set.ncard_prod, ncard_weightBits]
  · rw [if_neg h]
    have heq : {qt : List Bool × List Bool |
      qt.1 ∈ PrefixBits r ∧
        qt.2 ∈ WeightBits (2 * (j - r) - 3) (j - r) ∧ 3 ≤ j - r} = ∅ := by
      ext qt
      simp [h]
    rw [heq]
    simp

end OeisA108081

namespace OeisA108081

/--
[prefixBits_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma prefixBits_recurrence
  {j : ℕ} :
-- imply
  (2 * j - 1).choose j = (PrefixBits j).ncard + ∑ r : Fin (j + 1), if 3 ≤ j - (r : ℕ) then (PrefixBits r).ncard * (2 * (j - r) - 3).choose (j - r) else 0 := by
-- proof
  rw [← ncard_allPrefixBits, ncard_allPrefix_eq_prefix_add_bad,
    ncard_badPairs]

end OeisA108081

namespace OeisA108081

/--
[prefixBits_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma prefixBits_finite
  {j : ℕ} :
-- imply
  (PrefixBits j).Finite := by
-- proof
  apply (List.finite_length_eq Bool (2 * j)).subset
  intro p hp
  exact hp.1

end OeisA108081

namespace OeisA108081

/--
[suffixBits_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma suffixBits_finite
  {k : ℕ} :
-- imply
  (SuffixBits k).Finite := by
-- proof
  apply (List.finite_length_eq Bool (2 * k)).subset
  intro s hs
  exact hs.1

end OeisA108081

namespace OeisA108081

/--
[canonicalPairs_eq_iUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma canonicalPairs_eq_iUnion
  {m : ℕ} :
-- imply
  CanonicalPairs m = ⋃ j : Fin (m + 1), PrefixBits j ×ˢ SuffixBits (m - j) := by
-- proof
  ext ps
  obtain ⟨p, s⟩ := ps
  rw [canonicalPair_iff_crossingFree]
  constructor
  · rintro ⟨hp, hs, hlen, hp0, hs0, hfree⟩
    let j := p.count true
    have hp_len : p.length = 2 * j := by
      unfold BitBalanced at hp
      omega
    have hj : j < m + 1 := by
      unfold BitBalanced at hs
      omega
    rw [Set.mem_iUnion]
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [Set.mem_prod]
    constructor
    · exact ⟨hp_len, hp, hp0, hfree⟩
    · have hjle : j ≤ m := by omega
      rw [hp_len] at hlen
      have hs_len : s.length = 2 * (m - j) := by
        omega
      exact ⟨hs_len, hs, hs0⟩
  · rw [Set.mem_iUnion]
    rintro ⟨j, hj⟩
    rw [Set.mem_prod, PrefixBits, SuffixBits, Set.mem_setOf_eq] at hj
    obtain ⟨⟨hpl, hp, hp0, hfree⟩, hsl, hs, hs0⟩ := hj
    simp only [Prod.fst, Prod.snd] at hpl hp hp0 hfree hsl hs hs0
    refine ⟨hp, hs, ?_, hp0, hs0, hfree⟩
    have hjle : (j : ℕ) ≤ m := by omega
    omega

end OeisA108081

namespace OeisA108081

/--
[pairLayers_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma pairLayers_disjoint
  {m : ℕ} :
-- imply
  Pairwise (Function.onFun Disjoint (fun j : Fin (m + 1) => PrefixBits j ×ˢ SuffixBits (m - j))) := by
-- proof
  intro i j hij
  change Disjoint (PrefixBits (i : ℕ) ×ˢ SuffixBits (m - (i : ℕ)))
    (PrefixBits (j : ℕ) ×ˢ SuffixBits (m - (j : ℕ)))
  rw [Set.disjoint_left]
  intro ps hi hj
  obtain ⟨p, s⟩ := ps
  rw [Set.mem_prod] at hi hj
  have hil := hi.1.1
  have hjl := hj.1.1
  exfalso
  apply hij
  apply Fin.ext
  omega

end OeisA108081

namespace OeisA108081

/--
[ncard_canonicalPairs_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_canonicalPairs_convolution
  {m : ℕ} :
-- imply
  (CanonicalPairs m).ncard = ∑ j : Fin (m + 1), (PrefixBits j).ncard * (SuffixBits (m - j)).ncard := by
-- proof
  rw [canonicalPairs_eq_iUnion]
  have hu := Set.ncard_iUnion_of_finite
    (ι := Fin (m + 1))
    (s := fun j : Fin (m + 1) => PrefixBits j ×ˢ SuffixBits (m - j))
    (fun j => (prefixBits_finite j).prod (suffixBits_finite (m - j)))
    (pairLayers_disjoint m)
  rw [hu, finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro j hj
  exact Set.ncard_prod

end OeisA108081

namespace OeisA108081

/--
[ncard_canonicalPairs_convolution_choose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_canonicalPairs_convolution_choose
  {m : ℕ} :
-- imply
  (CanonicalPairs m).ncard = ∑ j : Fin (m + 1), (PrefixBits j).ncard * (2 * (m - j) - 1).choose (m - j) := by
-- proof
  rw [ncard_canonicalPairs_convolution]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ncard_suffixBits]

end OeisA108081

namespace OeisA108081

/--
[TreeBits_subset_CenteredTreeBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma TreeBits_subset_CenteredTreeBits
  {m : ℕ} :
-- imply
  TreeBits m ⊆ CenteredTreeBits m := by
-- proof
  rintro b ⟨w, hw, rfl⟩
  rw [coordXN, Set.mem_setOf_eq] at hw
  rw [CenteredTreeBits, Set.mem_setOf_eq]
  refine ⟨coordsToBits_mem_forestBits hw.2 hw.1.forestForm, ?_⟩
  obtain ⟨L, R, hL, hR, rfl⟩ := coordInsert_iff_forest_decomp.mp hw.1
  obtain hLnil | ⟨Lp, q, hLeq⟩ := List.eq_nil_or_concat L
  · subst L
    cases R with
    | nil =>
      refine ⟨[], [], ?_, ?_, ?_⟩
      · decide
      · simp [BitBalanced]
      · simp [BitBalanced]
    | cons r Rs =>
      have hm : coordMovementBit (0, false) r = false :=
        movement_to_right_forest hR (by simp) rfl
      refine ⟨[], coordsToBits (r :: Rs) ++ [false], ?_, ?_,
        balanced_pad_right_of_true_forest rfl hR (by simp)⟩
      · simp [coordsToBits_append_bridge, coordsToBits, hm, List.append_assoc]
      · simp [BitBalanced]
  · subst L
    have hLne : Lp.concat q ≠ [] := by simp
    have hmL : coordMovementBit q (0, false) = false :=
      movement_from_left_forest hL hLne (by simp)
    cases R with
    | nil =>
      refine ⟨false :: coordsToBits (Lp.concat q), [], ?_,
        balanced_pad_left_of_true_forest rfl hL hLne, ?_⟩
      · rw [show Lp.concat q ++ [(0, false)] =
        (Lp ++ [q]) ++ (0, false) :: [] by simp [List.concat_eq_append]]
        rw [coordsToBits_append_bridge]
        simp [coordsToBits, hmL, List.concat_eq_append, List.append_assoc]
      · simp [BitBalanced]
    | cons r Rs =>
      have hmR : coordMovementBit (0, false) r = false :=
        movement_to_right_forest hR (by simp) rfl
      refine ⟨false :: coordsToBits (Lp.concat q),
        coordsToBits (r :: Rs) ++ [false], ?_,
        balanced_pad_left_of_true_forest rfl hL hLne,
        balanced_pad_right_of_true_forest rfl hR (by simp)⟩
      rw [show Lp.concat q ++ (0, false) :: r :: Rs =
        (Lp ++ [q]) ++ (0, false) :: r :: Rs by simp [List.concat_eq_append]]
      rw [coordsToBits_append_bridge Lp (r :: Rs) q (0, false)]
      rw [show (0, false) :: r :: Rs =
        (([] ++ [(0, false)]) ++ r :: Rs) by rfl]
      rw [coordsToBits_append_bridge [] Rs (0, false) r]
      simp [coordsToBits, hmL, hmR, List.concat_eq_append, List.append_assoc]
open PowerSeries

end OeisA108081

namespace OeisA108081

/--
[suffixSeries_catalan_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma suffixSeries_catalan_step
  {r : ℕ} :
-- imply
  suffixSeries * PowerSeries.catalanSeries ^ (r + 1) = suffixSeries * PowerSeries.catalanSeries ^ r + PowerSeries.X * (suffixSeries * PowerSeries.catalanSeries ^ (r + 2)) := by
-- proof
  have hC : catalanSeries = 1 + X * catalanSeries ^ 2 := by
    calc
      catalanSeries = catalanSeries ^ 2 * X + 1 :=
        catalanSeries_sq_mul_X_add_one.symm
      _ = 1 + X * catalanSeries ^ 2 := by ring
  calc
    suffixSeries * catalanSeries ^ (r + 1) =
      (suffixSeries * catalanSeries ^ r) * catalanSeries := by ring
    _ = (suffixSeries * catalanSeries ^ r) *
      (1 + X * catalanSeries ^ 2) :=
      congrArg (fun z => (suffixSeries * catalanSeries ^ r) * z) hC
    _ = suffixSeries * catalanSeries ^ r +
      X * (suffixSeries * catalanSeries ^ (r + 2)) := by ring

end OeisA108081

namespace OeisA108081

/--
[coeff_suffixSeries_mul_catalan_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_suffixSeries_mul_catalan_pow
  {k r : ℕ} :
-- imply
  PowerSeries.coeff k (suffixSeries * PowerSeries.catalanSeries ^ r) = (2 * k + r - 1).choose k := by
-- proof
  induction k using Nat.strong_induction_on generalizing r with
  | h k ih =>
    induction r with
    | zero => simp [suffixSeries]
    | succ r hr =>
      rw [suffixSeries_catalan_step r]
      simp only [map_add]
      cases k with
      | zero =>
        rw [hr]
        have hz : coeff 0
          (X * (suffixSeries * catalanSeries ^ (r + 2))) = 0 := by
          rw [PowerSeries.coeff_mul]
          simp
        rw [hz]
        simp
      | succ k =>
        rw [PowerSeries.X_mul, PowerSeries.coeff_succ_mul_X, hr,
          ih k (by omega) (r + 2)]
        have h1 : 2 * (k + 1) + r - 1 = 2 * k + r + 1 := by omega
        have h2 : 2 * k + (r + 2) - 1 = 2 * k + r + 1 := by omega
        have h3 : 2 * (k + 1) + (r + 1) - 1 = (2 * k + r + 1) + 1 := by omega
        rw [h1, h2, h3]
        calc
          (2 * k + r + 1).choose (k + 1) +
            (2 * k + r + 1).choose k =
            (2 * k + r + 1).choose k +
              (2 * k + r + 1).choose (k + 1) := by ac_rfl
          _ = ((2 * k + r + 1) + 1).choose (k + 1) :=
            (Nat.choose_succ_succ (2 * k + r + 1) k).symm

end OeisA108081

namespace OeisA108081

/--
[coeff_badSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_badSeries
  {n : ℕ} :
-- imply
  PowerSeries.coeff n badSeries = if 3 ≤ n then (2 * n - 3).choose n else 0 := by
-- proof
  rw [badSeries, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_suffixSeries_mul_catalan_pow]
    have ht : 2 * (n - 3) + 4 - 1 = 2 * n - 3 := by omega
    rw [ht]
    calc
      (2 * n - 3).choose (n - 3) =
        (2 * n - 3).choose ((2 * n - 3) - n) := by congr 1 <;> omega
      _ = (2 * n - 3).choose n := Nat.choose_symm (by omega)
  · rfl

end OeisA108081

namespace OeisA108081

/--
[prefixSeries_mul_one_add_badSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma prefixSeries_mul_one_add_badSeries
-- imply
  prefixSeries * (1 + badSeries) = suffixSeries := by
-- proof
  ext j
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range]
  simp only [Prod.fst, Prod.snd, map_add, PowerSeries.coeff_one,
    coeff_badSeries, prefixSeries, suffixSeries, PowerSeries.coeff_mk]
  rw [prefixBits_recurrence j]
  simp_rw [mul_add, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib]
  have hone : (∑ x : Fin (j + 1),
    (if j - (x : ℕ) = 0 then (PrefixBits x).ncard else 0 : ℕ)) =
    (PrefixBits j).ncard := by
    rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (j + 1))]
    · simp
    · intro b hb hne
      have hb_le : (b : ℕ) ≤ j := by have := b.isLt; omega
      have hb_ne : (b : ℕ) ≠ j := by
        intro he
        apply hne
        apply Fin.ext
        exact he
      rw [if_neg (by omega)]
    · simp
  rw [hone]

end OeisA108081

namespace OeisA108081

/--
[suffixSeries_mul_catalan_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma suffixSeries_mul_catalan_add_one
-- imply
  suffixSeries * PowerSeries.catalanSeries + 1 = suffixSeries + suffixSeries := by
-- proof
  ext n
  simp only [map_add, PowerSeries.coeff_one]
  rw [show suffixSeries * catalanSeries =
    suffixSeries * catalanSeries ^ 1 by ring,
    coeff_suffixSeries_mul_catalan_pow]
  simp only [suffixSeries, PowerSeries.coeff_mk]
  cases n with
  | zero => simp
  | succ n =>
    rw [if_neg (by omega), add_zero]
    have hp := Nat.choose_succ_succ (2 * n + 1) n
    have hs : (2 * n + 1).choose n = (2 * n + 1).choose (n + 1) := by
      rw [← Nat.choose_symm (n := 2 * n + 1) (k := n) (by omega)]
      congr 2 <;> omega
    rw [hs] at hp
    have ha : 2 * (n + 1) + 1 - 1 = (2 * n + 1) + 1 := by omega
    have hb : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    rwa [ha, hb]

end OeisA108081

namespace OeisA108081

/--
[one_add_badSeries_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma one_add_badSeries_relation
-- imply
  1 + badSeries + suffixSeries * catalanTreeSeries + suffixSeries * catalanTreeSeries ^ 2 = suffixSeries := by
-- proof
  have hC : catalanSeries = 1 + X * catalanSeries ^ 2 := by
    calc
      catalanSeries = catalanSeries ^ 2 * X + 1 :=
        catalanSeries_sq_mul_X_add_one.symm
      _ = 1 + X * catalanSeries ^ 2 := by ring
  have hSCexpand : suffixSeries * catalanSeries =
    suffixSeries + X * suffixSeries * catalanSeries ^ 2 := by
    calc
      suffixSeries * catalanSeries =
        suffixSeries * (1 + X * catalanSeries ^ 2) :=
        congrArg (fun z => suffixSeries * z) hC
      _ = _ := by ring
  have hsmall_eq : suffixSeries +
    (1 + X * suffixSeries * catalanSeries ^ 2) =
    suffixSeries + suffixSeries := by
    calc
      suffixSeries + (1 + X * suffixSeries * catalanSeries ^ 2) =
        (suffixSeries + X * suffixSeries * catalanSeries ^ 2) + 1 := by ring
      _ = suffixSeries * catalanSeries + 1 := by rw [hSCexpand]
      _ = suffixSeries + suffixSeries := suffixSeries_mul_catalan_add_one
  have hsmall : 1 + X * suffixSeries * catalanSeries ^ 2 =
    suffixSeries := by
    apply PowerSeries.ext
    intro n
    have hn : coeff n suffixSeries +
      coeff n (1 + X * suffixSeries * catalanSeries ^ 2) =
      coeff n suffixSeries + coeff n suffixSeries := by
      simpa only [map_add] using congrArg (fun z => coeff n z) hsmall_eq
    exact Nat.add_left_cancel hn
  calc
    1 + badSeries + suffixSeries * catalanTreeSeries +
      suffixSeries * catalanTreeSeries ^ 2 =
      1 + X * suffixSeries * catalanSeries ^ 2 := by
      rw [badSeries, catalanTreeSeries]
      calc
        1 + X ^ 3 * (suffixSeries * catalanSeries ^ 4) +
          suffixSeries * (X * catalanSeries) +
          suffixSeries * (X * catalanSeries) ^ 2 =
          1 + X * suffixSeries * catalanSeries *
            (1 + X * catalanSeries + X ^ 2 * catalanSeries ^ 3) := by ring
        _ = 1 + X * suffixSeries * catalanSeries *
          (1 + X * catalanSeries * (1 + X * catalanSeries ^ 2)) := by ring
        _ = 1 + X * suffixSeries * catalanSeries *
          (1 + X * catalanSeries * catalanSeries) := by rw [← hC]
        _ = 1 + X * suffixSeries * catalanSeries *
          (1 + X * catalanSeries ^ 2) := by ring
        _ = 1 + X * suffixSeries * catalanSeries * catalanSeries := by rw [← hC]
        _ = 1 + X * suffixSeries * catalanSeries ^ 2 := by ring
    _ = suffixSeries := hsmall

end OeisA108081

namespace OeisA108081

/--
[constantCoeff_badSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma constantCoeff_badSeries
-- imply
  PowerSeries.constantCoeff badSeries = 0 := by
-- proof
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_badSeries]
  simp

end OeisA108081

namespace OeisA108081

/--
[prefixSeries_fibonacci_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma prefixSeries_fibonacci_equation
-- imply
  prefixSeries = 1 + prefixSeries * catalanTreeSeries + prefixSeries * catalanTreeSeries ^ 2 := by
-- proof
  let U : PowerSeries ℕ := 1 + badSeries
  let Q : PowerSeries ℕ := 1 + prefixSeries * catalanTreeSeries +
    prefixSeries * catalanTreeSeries ^ 2
  have hfac : Q * U = prefixSeries * U := by
    dsimp [Q, U]
    calc
      (1 + prefixSeries * catalanTreeSeries +
        prefixSeries * catalanTreeSeries ^ 2) * (1 + badSeries) =
        (1 + badSeries) + (prefixSeries * (1 + badSeries)) *
          catalanTreeSeries + (prefixSeries * (1 + badSeries)) *
            catalanTreeSeries ^ 2 := by ring
      _ = 1 + badSeries + suffixSeries * catalanTreeSeries +
        suffixSeries * catalanTreeSeries ^ 2 := by
        rw [prefixSeries_mul_one_add_badSeries]
      _ = suffixSeries := one_add_badSeries_relation
      _ = prefixSeries * (1 + badSeries) :=
        prefixSeries_mul_one_add_badSeries.symm
  apply (PowerSeries.map_injective (Nat.castRingHom ℤ) Nat.cast_injective)
  have hc : PowerSeries.constantCoeff
    (PowerSeries.map (Nat.castRingHom ℤ) U) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [U, constantCoeff_badSeries]
  have hu : IsUnit (PowerSeries.map (Nat.castRingHom ℤ) U) := by
    rwa [PowerSeries.isUnit_iff_constantCoeff, hc]
  apply hu.mul_right_cancel
  simpa only [map_mul] using
    congrArg (PowerSeries.map (Nat.castRingHom ℤ)) hfac.symm

end OeisA108081

namespace OeisA108081

/--
[treeCountSeries_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma treeCountSeries_equation
-- imply
  treeCountSeries = suffixSeries + treeCountSeries * catalanTreeSeries + treeCountSeries * catalanTreeSeries ^ 2 := by
-- proof
  calc
    treeCountSeries = prefixSeries * suffixSeries := rfl
    _ = (1 + prefixSeries * catalanTreeSeries +
      prefixSeries * catalanTreeSeries ^ 2) * suffixSeries :=
      congrArg (fun z => z * suffixSeries) prefixSeries_fibonacci_equation
    _ = suffixSeries + treeCountSeries * catalanTreeSeries +
      treeCountSeries * catalanTreeSeries ^ 2 := by
      rw [treeCountSeries]
      ring

end OeisA108081

namespace OeisA108081

/--
[treeCountSeries_equation_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma treeCountSeries_equation_step
-- imply
  treeCountSeries = suffixSeries + treeCountSeries * treeStepSeries := by
-- proof
  calc
    treeCountSeries = suffixSeries + treeCountSeries * catalanTreeSeries +
      treeCountSeries * catalanTreeSeries ^ 2 := treeCountSeries_equation
    _ = suffixSeries + treeCountSeries * treeStepSeries := by
      rw [treeStepSeries]
      ring

end OeisA108081

namespace OeisA108081

/--
[treeCountSeries_unroll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma treeCountSeries_unroll
  {N : ℕ} :
-- imply
  treeCountSeries = suffixSeries * (∑ i ∈ Finset.range (N + 1), treeStepSeries ^ i) + treeCountSeries * treeStepSeries ^ (N + 1) := by
-- proof
  induction N with
  | zero =>
    have hs : (∑ i ∈ Finset.range (0 + 1), treeStepSeries ^ i) = 1 := by simp
    rw [hs]
    simpa using treeCountSeries_equation_step
  | succ N ih =>
    calc
      treeCountSeries =
        suffixSeries * (∑ i ∈ Finset.range (N + 1), treeStepSeries ^ i) +
          treeCountSeries * treeStepSeries ^ (N + 1) := ih
      _ = suffixSeries * (∑ i ∈ Finset.range (N + 1), treeStepSeries ^ i) +
        (suffixSeries + treeCountSeries * treeStepSeries) *
          treeStepSeries ^ (N + 1) := by
        rw [← treeCountSeries_equation_step]
      _ = suffixSeries *
        (∑ i ∈ Finset.range (N + 2), treeStepSeries ^ i) +
        treeCountSeries * treeStepSeries ^ (N + 2) := by
        have hsum : (∑ i ∈ Finset.range (N + 2), treeStepSeries ^ i) =
          (∑ i ∈ Finset.range (N + 1), treeStepSeries ^ i) +
            treeStepSeries ^ (N + 1) := by
          rw [show N + 2 = (N + 1) + 1 by omega,
            Finset.sum_range_succ]
        have hp : treeStepSeries ^ (N + 2) =
          treeStepSeries * treeStepSeries ^ (N + 1) := by
          calc
            treeStepSeries ^ (N + 2) =
              treeStepSeries ^ (1 + (N + 1)) := by congr 1 <;> omega
            _ = treeStepSeries * treeStepSeries ^ (N + 1) := by
              rw [pow_add]
              simp
        rw [hsum, hp]
        ring

end OeisA108081

namespace OeisA108081

/--
[treeStepSeries_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma treeStepSeries_factor
-- imply
  treeStepSeries = PowerSeries.X * (PowerSeries.catalanSeries + PowerSeries.X * PowerSeries.catalanSeries ^ 2) := by
-- proof
  rw [treeStepSeries, catalanTreeSeries]
  ring

end OeisA108081

namespace OeisA108081

/--
[coeff_treeCount_mul_treeStep_pow_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_treeCount_mul_treeStep_pow_succ
  {m : ℕ} :
-- imply
  PowerSeries.coeff m (treeCountSeries * treeStepSeries ^ (m + 1)) = 0 := by
-- proof
  rw [treeStepSeries_factor, mul_pow]
  have heq : treeCountSeries *
    (PowerSeries.X ^ (m + 1) *
      (PowerSeries.catalanSeries +
        PowerSeries.X * PowerSeries.catalanSeries ^ 2) ^ (m + 1)) =
    PowerSeries.X ^ (m + 1) *
      (treeCountSeries * (PowerSeries.catalanSeries +
        PowerSeries.X * PowerSeries.catalanSeries ^ 2) ^ (m + 1)) := by ring
  rw [heq, PowerSeries.coeff_X_pow_mul']
  simp

end OeisA108081

namespace OeisA108081

/--
[coeff_treeCountSeries_as_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_treeCountSeries_as_step_sum
  {m : ℕ} :
-- imply
  PowerSeries.coeff m treeCountSeries = PowerSeries.coeff m (suffixSeries * (∑ i ∈ Finset.range (m + 1), treeStepSeries ^ i)) := by
-- proof
  have h := congrArg (fun z => PowerSeries.coeff m z)
    (treeCountSeries_unroll m)
  simpa [coeff_treeCount_mul_treeStep_pow_succ] using h

end OeisA108081

namespace OeisA108081

/--
[coeff_treeCountSeries_eq_centered_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_treeCountSeries_eq_centered_ncard
  {m : ℕ} :
-- imply
  PowerSeries.coeff m treeCountSeries = (CenteredTreeBits m).ncard := by
-- proof
  rw [treeCountSeries, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range]
  simp only [Prod.fst, Prod.snd, prefixSeries, suffixSeries,
    PowerSeries.coeff_mk]
  rw [ncard_centeredTreeBits, ncard_canonicalPairs_convolution_choose]

end OeisA108081

namespace OeisA108081

/--
[a_eq_catalan_coefficient_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma a_eq_catalan_coefficient_sum
  {m : ℕ} :
-- imply
  a m = ∑ k : Fin (m + 1), PowerSeries.coeff k (suffixSeries * PowerSeries.catalanSeries ^ (m - (k : ℕ))) * fib (m - (k : ℕ) + 1) := by
-- proof
  rw [a, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_suffixSeries_mul_catalan_pow]
  congr 2
  have hk_le : (k : ℕ) ≤ m := by have := k.isLt; omega
  omega

end OeisA108081

namespace OeisA108081

/--
[coeff_suffixSeries_mul_catalanTree_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_suffixSeries_mul_catalanTree_pow
  {k r : ℕ} :
-- imply
  PowerSeries.coeff k (suffixSeries * catalanTreeSeries ^ r) = if r ≤ k then (2 * (k - r) + r - 1).choose (k - r) else 0 := by
-- proof
  have heq : suffixSeries * catalanTreeSeries ^ r =
    PowerSeries.X ^ r *
      (suffixSeries * PowerSeries.catalanSeries ^ r) := by
    rw [catalanTreeSeries, mul_pow]
    ring
  rw [heq, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · exact coeff_suffixSeries_mul_catalan_pow (k - r) r
  · rfl

end OeisA108081

namespace OeisA108081

/--
[treeStepSeries_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma treeStepSeries_pow
  {i : ℕ} :
-- imply
  treeStepSeries ^ i = ∑ j ∈ Finset.range (i + 1), catalanTreeSeries ^ (2 * i - j) * (i.choose j) := by
-- proof
  rw [treeStepSeries, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [← pow_mul, ← pow_add]
  congr 2
  omega

end OeisA108081

namespace OeisA108081

/--
[fib_succ_eq_sum_choose_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma fib_succ_eq_sum_choose_fin
  {r : ℕ} :
-- imply
  fib (r + 1) = ∑ i : Fin (r + 1), (i : ℕ).choose (r - (i : ℕ)) := by
-- proof
  rw [Nat.fib_succ_eq_sum_choose,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range]

end OeisA108081

namespace OeisA108081

/--
[coeff_stepPolynomial_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_stepPolynomial_pow
  {i r : ℕ} :
-- imply
  ((Polynomial.X + Polynomial.X ^ 2) ^ i : Polynomial ℕ).coeff r = if i ≤ r then i.choose (r - i) else 0 := by
-- proof
  have hexp : ((Polynomial.X + Polynomial.X ^ 2) ^ i : Polynomial ℕ) =
    ∑ j ∈ Finset.range (i + 1),
      Polynomial.X ^ (2 * i - j) * Polynomial.C (i.choose j) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [← pow_mul, ← pow_add]
    change Polynomial.X ^ (j + 2 * (i - j)) * Polynomial.C (i.choose j) = _
    congr 2
    omega
  rw [hexp]
  change Polynomial.lcoeff ℕ r
    (∑ j ∈ Finset.range (i + 1),
      Polynomial.X ^ (2 * i - j) * Polynomial.C (i.choose j)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply]
  simp_rw [show ∀ d a : ℕ,
    (Polynomial.X ^ d * Polynomial.C a : Polynomial ℕ).coeff r =
      if d = r then a else 0 by
    intro d a
    simp [Polynomial.coeff_X_pow, eq_comm]]
  by_cases hir : i ≤ r
  · rw [if_pos hir]
    by_cases hri : r ≤ 2 * i
    · rw [Finset.sum_eq_single (2 * i - r)]
      · have hx : 2 * i - (2 * i - r) = r := by omega
        rw [if_pos hx]
        have hj : 2 * i - r ≤ i := by omega
        rw [← Nat.choose_symm hj]
        congr 1
        omega
      · intro b hb hne
        rw [if_neg]
        have hb' := Finset.mem_range.mp hb
        omega
      · intro hnot
        exfalso
        apply hnot
        rw [Finset.mem_range]
        omega
    · have hc : i.choose (r - i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hc]
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg]
      omega
  · rw [if_neg hir]
    apply Finset.sum_eq_zero
    intro b hb
    rw [if_neg]
    have hb' := Finset.mem_range.mp hb
    omega

end OeisA108081

namespace OeisA108081

/--
[coeff_geom_stepPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_geom_stepPolynomial
  {m r : ℕ}
-- given
  (hr : r ≤ m) :
-- imply
  (∑ i ∈ Finset.range (m + 1), ((Polynomial.X + Polynomial.X ^ 2) ^ i : Polynomial ℕ)).coeff r = fib (r + 1) := by
-- proof
  change Polynomial.lcoeff ℕ r
    (∑ i ∈ Finset.range (m + 1),
      ((Polynomial.X + Polynomial.X ^ 2) ^ i : Polynomial ℕ)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, coeff_stepPolynomial_pow]
  rw [← Finset.sum_filter]
  rw [show (Finset.range (m + 1)).filter (fun i => i ≤ r) =
    Finset.range (r + 1) by
    ext i
    simp
    omega]
  rw [fib_succ_eq_sum_choose_fin, Finset.sum_range]

end OeisA108081

namespace OeisA108081

/--
[coeff_fibPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_fibPolynomial
  {m r : ℕ}
-- given
  (hr : r ≤ m) :
-- imply
  (fibPolynomial m).coeff r = fib (r + 1) := by
-- proof
  rw [fibPolynomial]
  change Polynomial.lcoeff ℕ r
    (∑ j ∈ Finset.range (m + 1),
      Polynomial.C (fib (j + 1)) * Polynomial.X ^ j) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply]
  rw [Finset.sum_eq_single r]
  · simp
  · intro b hb hne
    simp [hne, Ne.symm hne]
  · intro hnot
    exfalso
    apply hnot
    simp
    omega

end OeisA108081

namespace OeisA108081

/--
[geom_sub_fibPolynomial_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma geom_sub_fibPolynomial_dvd
  {m : ℕ} :
-- imply
  (Polynomial.X : Polynomial ℤ) ^ (m + 1) ∣ (geomStepPolynomial m).map (Nat.castRingHom ℤ) - (fibPolynomial m).map (Nat.castRingHom ℤ) := by
-- proof
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, Polynomial.coeff_map,
    Polynomial.coeff_map]
  rw [show (geomStepPolynomial m).coeff d = fib (d + 1) by
    exact coeff_geom_stepPolynomial m d (by omega),
    coeff_fibPolynomial m d (by omega)]
  simp

end OeisA108081

namespace OeisA108081

/--
[coeff_step_geometric_eq_fibTreePartial_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_step_geometric_eq_fibTreePartial_le
  {m r : ℕ}
-- given
  (hr : r ≤ m) :
-- imply
  PowerSeries.coeff r (∑ i ∈ Finset.range (m + 1), treeStepSeries ^ i) = PowerSeries.coeff r (fibTreePartialSeries m) := by
-- proof
  let castPS : PowerSeries ℕ →+* PowerSeries ℤ :=
    PowerSeries.map (Nat.castRingHom ℤ)
  let t : PowerSeries ℤ := castPS catalanTreeSeries
  obtain ⟨q, hq⟩ := geom_sub_fibPolynomial_dvd m
  have hzero : PowerSeries.coeff r
    (Polynomial.eval₂ PowerSeries.C t
      ((Polynomial.X : Polynomial ℤ) ^ (m + 1) * q)) = 0 := by
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [show t ^ (m + 1) = PowerSeries.X ^ (m + 1) *
      (PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries) ^
        (m + 1) by
      dsimp [t, castPS]
      rw [catalanTreeSeries, map_mul, PowerSeries.map_X, mul_pow]]
    rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
    exact if_neg (by omega)
  have hdifference : PowerSeries.coeff r
    (Polynomial.eval₂ PowerSeries.C t
      ((geomStepPolynomial m).map (Nat.castRingHom ℤ) -
        (fibPolynomial m).map (Nat.castRingHom ℤ))) = 0 := by
    obtain ⟨q', hq'⟩ := geom_sub_fibPolynomial_dvd m
    rw [hq']
    have hqq : q' = q := by
      apply mul_left_cancel₀ (a := (Polynomial.X : Polynomial ℤ) ^ (m + 1))
      · simp
      · rw [← hq, ← hq']
    subst q'
    exact hzero
  have hevalGeom : Polynomial.eval₂ PowerSeries.C t
    ((geomStepPolynomial m).map (Nat.castRingHom ℤ)) =
    castPS (∑ i ∈ Finset.range (m + 1), treeStepSeries ^ i) := by
    rw [Polynomial.eval₂_map]
    change (Polynomial.eval₂RingHom (PowerSeries.C.comp (Nat.castRingHom ℤ)) t)
      (∑ i ∈ Finset.range (m + 1),
        (Polynomial.X + Polynomial.X ^ 2) ^ i) = _
    rw [map_sum]
    dsimp [castPS]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [map_pow, treeStepSeries, map_add, map_pow]
  have hevalFib : Polynomial.eval₂ PowerSeries.C t
    ((fibPolynomial m).map (Nat.castRingHom ℤ)) =
    castPS (fibTreePartialSeries m) := by
    rw [Polynomial.eval₂_map]
    change (Polynomial.eval₂RingHom (PowerSeries.C.comp (Nat.castRingHom ℤ)) t)
      (∑ x ∈ Finset.range (m + 1),
        Polynomial.C (fib (x + 1)) * Polynomial.X ^ x) = _
    rw [map_sum]
    dsimp [fibTreePartialSeries]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_pow, Polynomial.eval₂_X]
    dsimp [t, castPS]
    rw [map_mul, map_pow, PowerSeries.map_C]
    rfl
  rw [Polynomial.eval₂_sub, hevalGeom, hevalFib, map_sub,
    PowerSeries.coeff_map, PowerSeries.coeff_map] at hdifference
  have hcast := sub_eq_zero.mp hdifference
  exact Nat.cast_injective hcast

end OeisA108081

namespace OeisA108081

/--
[coeff_step_geometric_eq_fibTreePartial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_step_geometric_eq_fibTreePartial
  {m : ℕ} :
-- imply
  PowerSeries.coeff m (∑ i ∈ Finset.range (m + 1), treeStepSeries ^ i) = PowerSeries.coeff m (fibTreePartialSeries m) := by
-- proof
  let castPS : PowerSeries ℕ →+* PowerSeries ℤ :=
    PowerSeries.map (Nat.castRingHom ℤ)
  let t : PowerSeries ℤ := castPS catalanTreeSeries
  obtain ⟨q, hq⟩ := geom_sub_fibPolynomial_dvd m
  have hev := congrArg
    (Polynomial.eval₂ PowerSeries.C t) hq
  have hzero : PowerSeries.coeff m
    (Polynomial.eval₂ PowerSeries.C t
      ((Polynomial.X : Polynomial ℤ) ^ (m + 1) * q)) = 0 := by
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [show t ^ (m + 1) = PowerSeries.X ^ (m + 1) *
      (PowerSeries.map (Nat.castRingHom ℤ) PowerSeries.catalanSeries) ^
        (m + 1) by
      dsimp [t, castPS]
      rw [catalanTreeSeries, map_mul, PowerSeries.map_X, mul_pow]]
    rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
    exact if_neg (Nat.not_succ_le_self m)
  have hdifference : PowerSeries.coeff m
    (Polynomial.eval₂ PowerSeries.C t
      ((geomStepPolynomial m).map (Nat.castRingHom ℤ) -
        (fibPolynomial m).map (Nat.castRingHom ℤ))) = 0 := by
    rwa [hq]
  have hevalGeom : Polynomial.eval₂ PowerSeries.C t
    ((geomStepPolynomial m).map (Nat.castRingHom ℤ)) =
    castPS (∑ i ∈ Finset.range (m + 1), treeStepSeries ^ i) := by
    rw [Polynomial.eval₂_map]
    change (Polynomial.eval₂RingHom (PowerSeries.C.comp (Nat.castRingHom ℤ)) t)
      (∑ i ∈ Finset.range (m + 1),
        (Polynomial.X + Polynomial.X ^ 2) ^ i) = _
    rw [map_sum]
    dsimp [castPS]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [map_pow, treeStepSeries, map_add, map_pow]
  have hevalFib : Polynomial.eval₂ PowerSeries.C t
    ((fibPolynomial m).map (Nat.castRingHom ℤ)) =
    castPS (fibTreePartialSeries m) := by
    rw [Polynomial.eval₂_map]
    change (Polynomial.eval₂RingHom (PowerSeries.C.comp (Nat.castRingHom ℤ)) t)
      (∑ r ∈ Finset.range (m + 1),
        Polynomial.C (fib (r + 1)) * Polynomial.X ^ r) = _
    rw [map_sum]
    dsimp [fibTreePartialSeries]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_pow, Polynomial.eval₂_X]
    dsimp [t, castPS]
    rw [map_mul, map_pow, PowerSeries.map_C]
    rfl
  rw [Polynomial.eval₂_sub, hevalGeom, hevalFib, map_sub,
    PowerSeries.coeff_map, PowerSeries.coeff_map] at hdifference
  have hcast := sub_eq_zero.mp hdifference
  exact Nat.cast_injective hcast

end OeisA108081

namespace OeisA108081

/--
[coeff_suffix_mul_step_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_suffix_mul_step_geometric
  {m : ℕ} :
-- imply
  PowerSeries.coeff m (suffixSeries * (∑ i ∈ Finset.range (m + 1), treeStepSeries ^ i)) = PowerSeries.coeff m (suffixSeries * fibTreePartialSeries m) := by
-- proof
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [Prod.fst, Prod.snd]
  have hij' := Finset.mem_antidiagonal.mp hij
  rw [coeff_step_geometric_eq_fibTreePartial_le m j (by omega)]

end OeisA108081

namespace OeisA108081

/--
[coeff_suffix_mul_fibTree_term](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_suffix_mul_fibTree_term
  {m r : ℕ} :
-- imply
  PowerSeries.coeff m (suffixSeries * (PowerSeries.C (fib (r + 1)) * catalanTreeSeries ^ r)) = if r ≤ m then PowerSeries.coeff (m - r) (suffixSeries * PowerSeries.catalanSeries ^ r) * fib (r + 1) else 0 := by
-- proof
  have heq : suffixSeries *
    (PowerSeries.C (fib (r + 1)) * catalanTreeSeries ^ r) =
    PowerSeries.X ^ r *
      ((suffixSeries * PowerSeries.catalanSeries ^ r) *
        PowerSeries.C (fib (r + 1))) := by
    rw [catalanTreeSeries, mul_pow]
    ring
  rw [heq, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [PowerSeries.coeff_mul_C]
  · rfl

end OeisA108081

namespace OeisA108081

/--
[coeff_suffix_mul_fibPartial_eq_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_suffix_mul_fibPartial_eq_a
  {m : ℕ} :
-- imply
  PowerSeries.coeff m (suffixSeries * fibTreePartialSeries m) = a m := by
-- proof
  rw [a_eq_catalan_coefficient_sum]
  rw [fibTreePartialSeries, Finset.mul_sum]
  rw [map_sum]
  simp_rw [coeff_suffix_mul_fibTree_term]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => PowerSeries.coeff k
      (suffixSeries * PowerSeries.catalanSeries ^ (m - k)) *
        fib (m - k + 1)) (m + 1)]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro x hx
  have hxle : x ≤ m := by simp at hx; omega
  have hcond : m + 1 - 1 - x ≤ m := by omega
  rw [if_pos hcond]
  congr 3 <;> omega

end OeisA108081

namespace OeisA108081

/--
[ncard_centeredTreeBits_eq_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma ncard_centeredTreeBits_eq_a
  {m : ℕ} :
-- imply
  (CenteredTreeBits m).ncard = a m := by
-- proof
  rw [← coeff_treeCountSeries_eq_centered_ncard]
  rw [coeff_treeCountSeries_as_step_sum]
  rw [coeff_suffix_mul_step_geometric]
  exact coeff_suffix_mul_fibPartial_eq_a m

end OeisA108081

namespace OeisA108081

/--
[coeff_step_geometric_eq_fibTreePartial_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coeff_step_geometric_eq_fibTreePartial_diag
  {m : ℕ} :
-- imply
  PowerSeries.coeff m (∑ i ∈ Finset.range (m + 1), treeStepSeries ^ i) = PowerSeries.coeff m (fibTreePartialSeries m) :=
-- proof
  coeff_step_geometric_eq_fibTreePartial_le m m le_rfl
@[simp] lemma coordLeft_ne (q : EdgeCoord) : coordLeft q ≠ q := by
  obtain ⟨k, e⟩ := q
  cases e <;> simp [coordLeft]
@[simp] lemma coordRight_ne (q : EdgeCoord) : coordRight q ≠ q := by
  obtain ⟨k, e⟩ := q
  cases e <;> simp [coordRight]
@[simp] lemma coordLeft_coordLeft (q : EdgeCoord) :
  coordLeft (coordLeft q) = q := by
  obtain ⟨k, e⟩ := q
  cases e <;> rfl
@[simp] lemma coordRight_coordRight (q : EdgeCoord) :
  coordRight (coordRight q) = q := by
  obtain ⟨k, e⟩ := q
  cases e <;> simp [coordRight]

end OeisA108081

namespace OeisA108081

/--
[CoordForestForm.head_eq_root_or_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForestForm.head_eq_root_or_left
  {root q : EdgeCoord}
  {s : List EdgeCoord}
-- given
  (hw : CoordForestForm root (q :: s)) :
-- imply
  q = root ∨ q = coordLeft root := by
-- proof
  obtain hnil | ⟨hp, hh, hl⟩ := hw
  · simp at hnil
  · rcases root with ⟨k, e⟩
    obtain ⟨j, f⟩ := q
    cases e <;> cases f <;>
      simp [coordLeft] at hh ⊢ <;> omega

end OeisA108081

namespace OeisA108081

/--
[CoordForestForm.last_eq_root_or_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForestForm.last_eq_root_or_right
  {root q : EdgeCoord}
  {p : List EdgeCoord}
-- given
  (hw : CoordForestForm root (p ++ [q])) :
-- imply
  q = root ∨ q = coordRight root := by
-- proof
  obtain hnil | ⟨hp, hh, hl⟩ := hw
  · simp at hnil
  · have hlast : (p ++ [q]).getLast?.map rightIndex =
    some (rightIndex root) := hl
    simp only [List.getLast?_concat, Option.map_some, Option.some.injEq] at hlast
    obtain ⟨k, e⟩ := root
    obtain ⟨j, f⟩ := q
    cases e <;> cases f <;>
      simp [coordRight, rightIndex] at hlast ⊢ <;> omega

end OeisA108081

namespace OeisA108081

/--
[coordPath_iff_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordPath_iff_isChain
  {w : List EdgeCoord} :
-- imply
  CoordPath w ↔ List.IsChain CoordAdjacent w := by
-- proof
  constructor
  · intro h
    induction h with
    | nil => simp [List.IsChain]
    | singleton q => simp [List.IsChain]
    | cons hqr hrs ih => simpa [List.IsChain] using ⟨hqr, ih⟩
  · intro h
    induction w with
    | nil => exact CoordPath.nil
    | cons q t ih =>
      cases t with
      | nil => exact CoordPath.singleton q
      | cons r s =>
        rw [List.isChain_cons] at h
        exact CoordPath.cons (by simpa using h.1 r rfl) (ih h.2)

end OeisA108081

namespace OeisA108081

/--
[coordLeft_mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordLeft_mem_leftSide
  {root : EdgeCoord} :
-- imply
  CoordLeftSide root (coordLeft root) := by
-- proof
  obtain ⟨k, e⟩ := root
  cases e <;> simp [CoordLeftSide, coordLeft]

end OeisA108081

namespace OeisA108081

/--
[leftSide_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma leftSide_step
  {root q r : EdgeCoord}
-- given
  (hq : CoordLeftSide root q)
  (hqn : q ≠ root)
  (hrn : r ≠ root)
  (hqr : CoordAdjacent q r) :
-- imply
  CoordLeftSide root r := by
-- proof
  obtain ⟨k, e⟩ := root
  obtain ⟨i, f⟩ := q
  obtain ⟨j, g⟩ := r
  cases e <;> cases f <;> cases g <;>
    simp [CoordLeftSide, CoordAdjacent, rightIndex] at * <;> omega

end OeisA108081

namespace OeisA108081

/--
[leftSide_end_before_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma leftSide_end_before_root
  {root q : EdgeCoord}
-- given
  (hq : CoordLeftSide root q)
  (hqn : q ≠ root)
  (hqr : CoordAdjacent q root) :
-- imply
  rightIndex q = rightIndex (coordLeft root) := by
-- proof
  obtain ⟨k, e⟩ := root
  obtain ⟨i, f⟩ := q
  cases e <;> cases f <;>
    simp [CoordLeftSide, CoordAdjacent, rightIndex, coordLeft] at * <;> omega

end OeisA108081

namespace OeisA108081

/--
[rightSide_of_root_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma rightSide_of_root_step
  {root r : EdgeCoord}
-- given
  (hr : r.1 ≠ root.1)
  (h : CoordAdjacent root r) :
-- imply
  CoordRightSide root r := by
-- proof
  obtain ⟨k, e⟩ := root
  obtain ⟨j, f⟩ := r
  cases e <;> cases f <;>
    simp [CoordRightSide, CoordAdjacent, rightIndex] at * <;> omega

end OeisA108081

namespace OeisA108081

/--
[rightSide_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma rightSide_step
  {root q r : EdgeCoord}
-- given
  (hq : CoordRightSide root q)
  (hr : r.1 ≠ root.1)
  (hqr : CoordAdjacent q r) :
-- imply
  CoordRightSide root r := by
-- proof
  obtain ⟨k, e⟩ := root
  obtain ⟨i, f⟩ := q
  obtain ⟨j, g⟩ := r
  cases e <;> cases f <;> cases g <;>
    simp [CoordRightSide, CoordAdjacent, rightIndex] at * <;> omega

end OeisA108081

namespace OeisA108081

/--
[rightSide_end_before_rootLevel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma rightSide_end_before_rootLevel
  {root q r : EdgeCoord}
-- given
  (hq : CoordRightSide root q)
  (hr : r.1 = root.1)
  (hqr : CoordAdjacent q r) :
-- imply
  rightIndex q = rightIndex (coordRight root) := by
-- proof
  obtain ⟨k, e⟩ := root
  obtain ⟨i, f⟩ := q
  obtain ⟨j, g⟩ := r
  cases e <;> cases f <;> cases g <;>
    simp [CoordRightSide, CoordAdjacent, rightIndex, coordRight] at * <;> omega

end OeisA108081

namespace OeisA108081

/--
[split_first_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma split_first_eq
  {a : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (ha : a ∈ w) :
-- imply
  ∃ L t, w = L ++ a :: t ∧ a ∉ L := by
-- proof
  induction w with
  | nil => simp at ha
  | cons q w ih =>
    by_cases hq : q = a
    · subst q
      exact ⟨[], w, rfl, by simp⟩
    · have haw : a ∈ w := (List.mem_cons.mp ha).resolve_left (Ne.symm hq)
      obtain ⟨L, t, heq, hnot⟩ := ih haw
      exact ⟨q :: L, t, by simp [heq], by
        simpa only [List.mem_cons, not_or] using And.intro (Ne.symm hq) hnot⟩

end OeisA108081

namespace OeisA108081

/--
[split_first_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma split_first_fst
  {k : ℤ}
  {w : List EdgeCoord} :
-- imply
  ∃ R v, w = R ++ v ∧ (∀ q ∈ R, q.1 ≠ k) ∧ (v = [] ∨ ∃ q s, v = q :: s ∧ q.1 = k) := by
-- proof
  induction w with
  | nil => exact ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | cons q w ih =>
    by_cases hq : q.1 = k
    · exact ⟨[], q :: w, rfl, by simp, Or.inr ⟨q, w, rfl, hq⟩⟩
    · rcases ih with ⟨R, v, heq, hR, hv⟩
      exact ⟨q :: R, v, by simp [heq], by simpa [hq] using hR, hv⟩

end OeisA108081

namespace OeisA108081

/--
[leftSide_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma leftSide_chain
  {root q : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hc : List.IsChain CoordAdjacent (q :: w))
  (hq : CoordLeftSide root q)
  (havoid : root ∉ q :: w) :
-- imply
  ∀ z ∈ q :: w, CoordLeftSide root z := by
-- proof
  induction w generalizing q with
  | nil => simpa using hq
  | cons r s ih =>
    rw [List.isChain_cons] at hc
    have hqr : CoordAdjacent q r := by simpa using hc.1 r rfl
    have hqn : q ≠ root := by
      intro he
      subst q
      exact havoid (by simp)
    have hrn : r ≠ root := by
      intro he
      subst r
      exact havoid (by simp)
    have hr := leftSide_step hq hqn hrn hqr
    intro z hz
    simp only [List.mem_cons] at hz
    obtain hz | hz := hz
    · subst z
      exact hq
    · exact ih hc.2 hr (fun hmem => havoid (List.mem_cons_of_mem q hmem))
      z (by simpa only [List.mem_cons] using hz)

end OeisA108081

namespace OeisA108081

/--
[rightSide_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma rightSide_chain
  {root q : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hc : List.IsChain CoordAdjacent (q :: w))
  (hq : CoordRightSide root q)
  (havoid : ∀ z ∈ q :: w, z.1 ≠ root.1) :
-- imply
  ∀ z ∈ q :: w, CoordRightSide root z := by
-- proof
  induction w generalizing q with
  | nil => simpa using hq
  | cons r s ih =>
    rw [List.isChain_cons] at hc
    have hqr : CoordAdjacent q r := by simpa using hc.1 r rfl
    have hr := rightSide_step hq (havoid r (by simp)) hqr
    intro z hz
    simp only [List.mem_cons] at hz
    obtain hz | hz := hz
    · subst z
      exact hq
    · exact ih hc.2 hr
      (fun y hy => havoid y (List.mem_cons_of_mem q hy)) z
      (by simpa only [List.mem_cons] using hz)

end OeisA108081

namespace OeisA108081

/--
[CoordPath.leftSide_of_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordPath.leftSide_of_avoids
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hp : CoordPath w)
  (hhead : w.head? = some (coordLeft root))
  (havoid : root ∉ w) :
-- imply
  ∀ q ∈ w, CoordLeftSide root q := by
-- proof
  cases w with
  | nil => simp
  | cons q w =>
    have hq : q = coordLeft root := by simpa using hhead
    subst q
    exact leftSide_chain (coordPath_iff_isChain.mp hp)
      (coordLeft_mem_leftSide root) havoid

end OeisA108081

namespace OeisA108081

/--
[CoordPath.rightSide_of_avoids_level](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordPath.rightSide_of_avoids_level
  {root : EdgeCoord}
  {q : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hp : CoordPath (root :: q :: w))
  (hq : q.1 ≠ root.1)
  (havoid : ∀ z ∈ q :: w, z.1 ≠ root.1) :
-- imply
  ∀ z ∈ q :: w, CoordRightSide root z := by
-- proof
  rw [coordPath_iff_isChain, List.isChain_cons] at hp
  have hqr : CoordAdjacent root q := by simpa using hp.1 q rfl
  exact rightSide_chain hp.2 (rightSide_of_root_step hq hqr) havoid

end OeisA108081

namespace OeisA108081

/--
[coordRight_not_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordRight_not_leftSide
  {root : EdgeCoord} :
-- imply
  ¬ CoordLeftSide root (coordRight root) := by
-- proof
  obtain ⟨k, e⟩ := root
  cases e <;> simp [CoordLeftSide, coordRight]

end OeisA108081

namespace OeisA108081

/--
[fst_eq_coordRight_of_adjacent_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma fst_eq_coordRight_of_adjacent_root
  {root q : EdgeCoord}
-- given
  (h : CoordAdjacent root q)
  (hne : q.1 ≠ root.1) :
-- imply
  q.1 = (coordRight root).1 := by
-- proof
  obtain ⟨k, e⟩ := root
  obtain ⟨j, f⟩ := q
  cases e <;> cases f <;>
    simp [CoordAdjacent, rightIndex, coordRight] at * <;> omega

end OeisA108081

namespace OeisA108081

/--
[coordForest_of_form_aux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coordForest_of_form_aux
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordForestForm root w) :
-- imply
  CoordForest root w := by
-- proof
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing root w with
  | h n ih =>
    by_cases hnil : w = []
    · subst w
      exact CoordForest.nil
    · rcases hw with hw0 | ⟨hp, hhead, hlast⟩
      · exact (hnil hw0).elim
      obtain ⟨q₀, s₀, rfl⟩ := List.exists_cons_of_ne_nil hnil
      have hfull : CoordForestForm root (q₀ :: s₀) := Or.inr ⟨hp, hhead, hlast⟩
      have hrootmem : root ∈ q₀ :: s₀ := by
        by_contra hnot
        have hq := (Or.resolve_left
          (CoordForestForm.head_eq_root_or_left hfull) (by
            intro he
            subst q₀
            exact hnot (by simp)))
        have hside : ∀ z ∈ q₀ :: s₀, CoordLeftSide root z :=
          hp.leftSide_of_avoids (by simpa [hq] using hhead) hnot
        obtain he | ⟨p, z, he⟩ := List.eq_nil_or_concat (q₀ :: s₀)
        · simp at he
        · have hclass : z = root ∨ z = coordRight root := by
          apply CoordForestForm.last_eq_root_or_right
            (root := root) (q := z) (p := p)
          simpa [List.concat_eq_append, he] using hfull
          have hzmem : z ∈ q₀ :: s₀ := by rw [he]; simp [List.concat_eq_append]
          obtain hz | hz := hclass
          · exact hnot (hz ▸ hzmem)
          · exact coordRight_not_leftSide root (hz ▸ hside z hzmem)
      obtain ⟨L, t, hwdecomp, hLavoid⟩ := split_first_eq hrootmem
      have hc : List.IsChain CoordAdjacent (L ++ root :: t) := by
        rw [← hwdecomp]
        exact coordPath_iff_isChain.mp hp
      have hcparts := List.isChain_append.mp hc
      have hchainL : List.IsChain CoordAdjacent L := hcparts.1
      have hchainRootTail : List.IsChain CoordAdjacent (root :: t) := hcparts.2.1
      have hLform : CoordForestForm (coordLeft root) L := by
        by_cases hLnil : L = []
        · exact Or.inl hLnil
        · right
          refine ⟨coordPath_iff_isChain.mpr hchainL, ?_, ?_⟩
          · have hwhead : (L ++ root :: t).head?.map Prod.fst = some root.1 := by
            simpa [hwdecomp] using hhead
            rw [List.head?_append_of_ne_nil _ hLnil] at hwhead
            simpa using hwhead
          · rcases List.eq_nil_or_concat L with hbad | ⟨p, q, hLeq⟩
            · contradiction
            · subst L
              have hadj : CoordAdjacent q root := by
                have hb := hcparts.2.2 q (by simp) root (by simp)
                exact hb
              have hq₀left : q₀ = coordLeft root := by
                apply Or.resolve_left (CoordForestForm.head_eq_root_or_left hfull)
                intro hqroot
                have hqmem : q₀ ∈ p.concat q := by
                  have hh : (p.concat q).head? = some q₀ := by
                    have hwhole := congrArg List.head? hwdecomp
                    simpa [List.head?_append_of_ne_nil _ (by simp : p.concat q ≠ [])] using hwhole.symm
                  exact List.mem_of_mem_head? hh
                exact hLavoid (hqroot ▸ hqmem)
              have hfirst : (p.concat q).head? = some (coordLeft root) := by
                have hwhole := congrArg List.head? hwdecomp
                simpa [List.head?_append_of_ne_nil _ (by simp : p.concat q ≠ []), hq₀left]
                  using hwhole.symm
              have hpL : CoordPath (p.concat q) := coordPath_iff_isChain.mpr hchainL
              have hsides := hpL.leftSide_of_avoids hfirst hLavoid
              have hqside : CoordLeftSide root q := hsides q (by simp)
              have hend := leftSide_end_before_root hqside
                (fun he => hLavoid (he ▸ (by simp))) hadj
              simpa [List.concat_eq_append, hend]
      obtain ⟨R, v, ht, hRavoid, hv⟩ := split_first_fst root.1 t
      have htailEq : root :: t = [root] ++ R ++ v := by simp [ht]
      have hcRV : List.IsChain CoordAdjacent (root :: R ++ v) := by
        simpa [ht] using hchainRootTail
      have hcSplit := List.isChain_append.mp hcRV
      have hchainRootR : List.IsChain CoordAdjacent (root :: R) := by
        simpa using hcSplit.1
      have hchainV : List.IsChain CoordAdjacent v := hcSplit.2.1
      have hRform : CoordForestForm (coordRight root) R := by
        by_cases hRnil : R = []
        · exact Or.inl hRnil
        · right
          obtain _ | ⟨q, s⟩ := R
          · contradiction
          · have hchainR : List.IsChain CoordAdjacent (q :: s) := by
            have := (List.isChain_cons.mp hchainRootR).2
            exact this
            have hadjRoot : CoordAdjacent root q := by
              exact (List.isChain_cons.mp hchainRootR).1 q rfl
            have hqne : q.1 ≠ root.1 := hRavoid q (by simp)
            have hsides : ∀ z ∈ q :: s, CoordRightSide root z := by
              have hpref : CoordPath (root :: q :: s) :=
                coordPath_iff_isChain.mpr hchainRootR
              exact hpref.rightSide_of_avoids_level hqne hRavoid
            refine ⟨coordPath_iff_isChain.mpr hchainR, ?_, ?_⟩
            · simp [fst_eq_coordRight_of_adjacent_root hadjRoot hqne]
            · rcases List.eq_nil_or_concat (q :: s) with hbad | ⟨p, z, hlastR⟩
              · simp at hbad
              · rcases hv with rfl | ⟨r, rs, hveq, hrfst⟩
                · have hglob := hlast
                  rw [hwdecomp, ht] at hglob
                  rw [List.append_nil] at hglob
                  rw [List.getLast?_append_of_ne_nil L (by simp : root :: q :: s ≠ [])] at hglob
                  rw [List.getLast?_cons_of_ne_nil (by simp : q :: s ≠ [])] at hglob
                  rwa [rightIndex_coordRight]
                · subst v
                  have hzlast : z ∈ (root :: q :: s).getLast? := by
                    rw [hlastR]
                    rw [List.getLast?_cons_of_ne_nil (by simp : p.concat z ≠ [])]
                    rw [List.concat_eq_append, List.getLast?_concat]
                    simp
                  have hadj : CoordAdjacent z r :=
                    hcSplit.2.2 z hzlast r (by simp)
                  have hzside : CoordRightSide root z := hsides z (by
                    rw [hlastR]
                    simp [List.concat_eq_append])
                  have hend := rightSide_end_before_rootLevel hzside hrfst hadj
                  rw [hlastR]
                  simp only [List.concat_eq_append, List.getLast?_concat,
                    Option.map_some, Option.some.injEq]
                  exact hend
      have hvform : CoordForestForm root v := by
        obtain rfl | ⟨q, s, hveq, hqfst⟩ := hv
        · exact Or.inl rfl
        · subst v
          right
          refine ⟨coordPath_iff_isChain.mpr hchainV, by simp [hqfst], ?_⟩
          have hglob := hlast
          rw [hwdecomp, ht] at hglob
          rw [List.getLast?_append_of_ne_nil L
            (by simp : root :: (R ++ q :: s) ≠ [])] at hglob
          rw [List.getLast?_cons_of_ne_nil (by simp : R ++ q :: s ≠ [])] at hglob
          rwa [List.getLast?_append_of_ne_nil R (by simp : q :: s ≠ [])] at hglob
      have hLlen : L.length < n := by
        have hlen := congrArg List.length hwdecomp
        simp only [List.length_cons, List.length_append] at hn hlen
        omega
      have hRlen : R.length < n := by
        have hlen1 := congrArg List.length hwdecomp
        have hlen2 := congrArg List.length ht
        simp only [List.length_cons, List.length_append] at hn hlen1 hlen2
        omega
      have hfL : CoordForest (coordLeft root) L :=
        ih L.length hLlen hLform rfl
      have hfR : CoordForest (coordRight root) R :=
        ih R.length hRlen hRform rfl
      have hfv : CoordForest root v := by
        have hvlen : v.length < n := by
          have hlen1 := congrArg List.length hwdecomp
          have hlen2 := congrArg List.length ht
          simp only [List.length_cons, List.length_append] at hn hlen1 hlen2
          omega
        exact ih v.length hvlen hvform rfl
      have htree : CoordTree root (L ++ root :: R) :=
        CoordRootDecomp.toTree ⟨L, R, hfL, hfR, rfl⟩
      rw [hwdecomp, ht]
      simpa [List.append_assoc] using CoordForest.cons htree hfv

end OeisA108081

namespace OeisA108081

/--
[CoordForestForm.exists_tree_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForestForm.exists_tree_prefix
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordForestForm root w)
  (hne : w ≠ []) :
-- imply
  ∃ u v, CoordTree root u ∧ CoordForestForm root v ∧ w = u ++ v ∧ v.length < w.length := by
-- proof
  have hf := coordForest_of_form_aux hw
  cases hf with
  | nil => exact (hne rfl).elim
  | @cons u v hu hv =>
    refine ⟨u, v, hu, hv.forestForm, rfl, ?_⟩
    have hupos : 0 < u.length := by
      apply Nat.pos_of_ne_zero
      intro hz
      have hunil : u = [] := List.length_eq_zero_iff.mp hz
      subst u
      have hh := CoordTree.head_fst hu
      simp at hh
    simp
    omega

end OeisA108081

namespace OeisA108081

/--
[CoordForest.of_forestForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CoordForest.of_forestForm
  {root : EdgeCoord}
  {w : List EdgeCoord}
-- given
  (hw : CoordForestForm root w) :
-- imply
  CoordForest root w := by
-- proof
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hne : w = []
    · subst w
      exact CoordForest.nil
    · rcases hw.exists_tree_prefix hne with ⟨u, v, hu, hv, heq, hlen⟩
      have hvn : v.length < n := by omega
      rw [heq]
      exact CoordForest.cons hu (ih v.length hvn hv rfl)

end OeisA108081

namespace OeisA108081

/--
[balancedPrefix_realize_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma balancedPrefix_realize_forest
  {p : List Bool}
-- given
  (hp : BitBalanced p)
  (hstart : p = [] ∨ p.head? = some false) :
-- imply
  ∃ L, CoordForest (0, true) L ∧ ((p = [] ∧ L = []) ∨ (L ≠ [] ∧ p = false :: coordsToBits L)) := by
-- proof
  obtain rfl | hstart := hstart
  · exact ⟨[], CoordForest.nil, Or.inl ⟨rfl, rfl⟩⟩
  · cases p with
    | nil => simp at hstart
    | cons e b =>
      have he : e = false := by simpa using hstart
      subst e
      let n := b.count true
      have hbal : 2 * n = b.length + 1 := by
        simpa [BitBalanced, n] using hp
      have hn : 0 < n := by
        by_contra hn
        have : n = 0 := by omega
        rw [this] at hbal
        omega
      let d := n - 1
      have hlen : b.length = 2 * d + 1 := by dsimp [d]; omega
      let L := bitsToCoords 0 b
      have hform : CoordForestForm (0, true) L := by
        right
        refine ⟨path_bitsToCoords 0 b, ?_, ?_⟩
        · cases b with
          | nil => simp at hlen
          | cons y t => simp [L, bitsToCoords]
        · rw [show L.getLast?.map rightIndex =
          some (0 + (d : ℤ) - (b.count true : ℤ)) by
          exact rightIndex_last_bitsToCoords 0 d b hlen]
          dsimp [d, n]
          simp [rightIndex]
          omega
      have hdecode : coordsToBits L = b := by
        dsimp [L]
        exact coordsToBits_bitsToCoords 0 d b hlen
      refine ⟨L, CoordForest.of_forestForm hform, Or.inr ⟨?_, ?_⟩⟩
      · intro hnil
        have := congrArg List.length hnil
        simp [L, length_bitsToCoords, hlen] at this
      · rw [hdecode]

end OeisA108081

namespace OeisA108081

/--
[balancedSuffix_realize_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma balancedSuffix_realize_forest
  {s : List Bool}
-- given
  (hs : BitBalanced s)
  (hend : s = [] ∨ s.getLast? = some false) :
-- imply
  ∃ R, CoordForest (1, true) R ∧ ((s = [] ∧ R = []) ∨ (R ≠ [] ∧ s = coordsToBits R ++ [false])) := by
-- proof
  obtain rfl | hend := hend
  · exact ⟨[], CoordForest.nil, Or.inl ⟨rfl, rfl⟩⟩
  · rcases List.eq_nil_or_concat s with rfl | ⟨b, e, rfl⟩
    · simp at hend
    · have he : e = false := by simpa [List.concat_eq_append] using hend
      subst e
      let n := b.count true
      have hbal : 2 * n = b.length + 1 := by
        simpa [BitBalanced, n, List.concat_eq_append] using hs
      have hn : 0 < n := by
        by_contra hn
        have : n = 0 := by omega
        rw [this] at hbal
        omega
      let d := n - 1
      have hlen : b.length = 2 * d + 1 := by dsimp [d]; omega
      let R := bitsToCoords 1 b
      have hform : CoordForestForm (1, true) R := by
        right
        refine ⟨path_bitsToCoords 1 b, ?_, ?_⟩
        · cases b with
          | nil => simp at hlen
          | cons y t => simp [R, bitsToCoords]
        · rw [show R.getLast?.map rightIndex =
          some (1 + (d : ℤ) - (b.count true : ℤ)) by
          exact rightIndex_last_bitsToCoords 1 d b hlen]
          dsimp [d, n]
          simp [rightIndex]
          omega
      have hdecode : coordsToBits R = b := by
        dsimp [R]
        exact coordsToBits_bitsToCoords 1 d b hlen
      refine ⟨R, CoordForest.of_forestForm hform, Or.inr ⟨?_, ?_⟩⟩
      · intro hnil
        have := congrArg List.length hnil
        simp [R, length_bitsToCoords, hlen] at this
      · simp [List.concat_eq_append, hdecode]

end OeisA108081

namespace OeisA108081

/--
[CenteredTreeBits_subset_TreeBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma CenteredTreeBits_subset_TreeBits
  {m : ℕ} :
-- imply
  CenteredTreeBits m ⊆ TreeBits m := by
-- proof
  intro b hb
  rw [CenteredTreeBits, Set.mem_setOf_eq] at hb
  obtain ⟨hfb, p, s, he, hp, hs⟩ := hb
  have hp0 := balanced_prefix_starts_false he
  have hs0 := balanced_suffix_ends_false he
  obtain ⟨L, hL, hLp⟩ := balancedPrefix_realize_forest hp hp0
  obtain ⟨R, hR, hRs⟩ := balancedSuffix_realize_forest hs hs0
  let w := L ++ (0, false) :: R
  have hwins : CoordInsert w := coordInsert_iff_forest_decomp.mpr
    ⟨L, R, hL, hR, rfl⟩
  have hout : false :: coordsToBits w ++ [false] =
    p ++ [false, false, false] ++ s := by
    dsimp [w]
    obtain ⟨rfl, rfl⟩ | ⟨hLne, rfl⟩ <;> := hLp
      obtain ⟨rfl, rfl⟩ | ⟨hRne, rfl⟩ := hRs
    · rfl
    · cases R with
      | nil => contradiction
      | cons r Rs =>
        have hm : coordMovementBit (0, false) r = false :=
          movement_to_right_forest hR (by simp) rfl
        simp [coordsToBits, hm, List.append_assoc]
    · rcases List.eq_nil_or_concat L with hnil | ⟨Lp, q, hLeq⟩
      · exact (hLne hnil).elim
      · subst L
        have hm : coordMovementBit q (0, false) = false :=
          movement_from_left_forest hL (by simp) (by
            simp [List.concat_eq_append])
        rw [show Lp.concat q ++ [(0, false)] =
          (Lp ++ [q]) ++ (0, false) :: [] by simp [List.concat_eq_append]]
        rw [coordsToBits_append_bridge]
        simp [w, coordsToBits, hm, List.concat_eq_append, List.append_assoc]
    · rcases List.eq_nil_or_concat L with hnil | ⟨Lp, q, hLeq⟩
      · exact (hLne hnil).elim
      · subst L
        cases R with
        | nil => contradiction
        | cons r Rs =>
          have hmL : coordMovementBit q (0, false) = false :=
            movement_from_left_forest hL (by simp) (by
              simp [List.concat_eq_append])
          have hmR : coordMovementBit (0, false) r = false :=
            movement_to_right_forest hR (by simp) rfl
          rw [show Lp.concat q ++ (0, false) :: r :: Rs =
            (Lp ++ [q]) ++ (0, false) :: r :: Rs by
              simp [List.concat_eq_append]]
          rw [coordsToBits_append_bridge Lp (r :: Rs) q (0, false)]
          rw [show (0, false) :: r :: Rs =
            (([] ++ [(0, false)]) ++ r :: Rs) by rfl]
          rw [coordsToBits_append_bridge [] Rs (0, false) r]
          simp [w, coordsToBits, hmL, hmR, List.concat_eq_append,
            List.append_assoc]
  have hbits : coordsToBits w = b := by
    have hh : false :: coordsToBits w ++ [false] = false :: b ++ [false] :=
      hout.trans he.symm
    exact List.append_cancel_right (List.cons.inj hh).2
  have hwlen : w.length = m + 1 := by
    have hpath := hwins.path
    have hlenbits := length_coordsToBits hpath
    rw [hbits] at hlenbits
    rw [ForestBits, Set.mem_setOf_eq] at hfb
    omega
  rw [TreeBits]
  exact ⟨w, ⟨hwins, hwlen⟩, hbits⟩

end OeisA108081

namespace OeisA108081

/--
[coord_enumeration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma coord_enumeration
  {m : ℕ} :
-- imply
  (coordXN (m + 1)).ncard = a m := by
-- proof
  rw [← ncard_TreeBits]
  rw [show TreeBits m = CenteredTreeBits m from
    Set.Subset.antisymm (TreeBits_subset_CenteredTreeBits m)
      (CenteredTreeBits_subset_TreeBits m)]
  exact ncard_centeredTreeBits_eq_a m

end OeisA108081

namespace OeisA108081

/--
[count_words_in_x_is_a_shifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
lemma count_words_in_x_is_a_shifted
  {n : ℕ} :
-- imply
  n ≥ 1 → Set.ncard (xN n) = a (n - 1) := by
-- proof
  intro hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [← ncard_coordXN]
  simpa [Nat.succ_eq_add_one] using coord_enumeration m

end OeisA108081

/--
[length_l](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma length_l_eq
  {w : Word} :
-- imply
  (l w).length = w.length := by
-- proof
  apply OeisA108081.length_l w

/--
[length_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma length_r_eq
  {w : Word} :
-- imply
  (r w).length = w.length := by
-- proof
  apply OeisA108081.length_r w

/--
[l_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma l_r_eq
  {w : Word} :
-- imply
  l (r w) = w := by
-- proof
  apply OeisA108081.l_r w

/--
[r_l](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma r_l_eq
  {w : Word} :
-- imply
  r (l w) = w := by
-- proof
  apply OeisA108081.r_l w

/--
[leftChild_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma leftChild_zero_eq :
-- imply
  leftChild 0 = -1 := by
-- proof
  apply OeisA108081.leftChild_zero

/--
[rightChild_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma rightChild_zero_eq :
-- imply
  rightChild 0 = 1 := by
-- proof
  apply OeisA108081.rightChild_zero

/--
[leftChild_leftChild](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma leftChild_leftChild_eq
  {z : ℤ} :
-- imply
  leftChild (leftChild z) = z := by
-- proof
  apply OeisA108081.leftChild_leftChild z

/--
[rightChild_rightChild](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma rightChild_rightChild_eq
  {z : ℤ} :
-- imply
  rightChild (rightChild z) = z := by
-- proof
  apply OeisA108081.rightChild_rightChild z

/--
[edgeValue_edgeCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma edgeValue_edgeCoord_eq
  {z : ℤ} :
-- imply
  edgeValue (edgeCoord z) = z := by
-- proof
  apply OeisA108081.edgeValue_edgeCoord z

/--
[edgeCoord_edgeValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma edgeCoord_edgeValue_eq
  {q : EdgeCoord} :
-- imply
  edgeCoord (edgeValue q) = q := by
-- proof
  apply OeisA108081.edgeCoord_edgeValue q

/--
[leftChild_edgeValue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma leftChild_edgeValue_false_eq
  {k : ℤ} :
-- imply
  leftChild (edgeValue (k, false)) = edgeValue (k, true) := by
-- proof
  apply OeisA108081.leftChild_edgeValue_false k

/--
[leftChild_edgeValue_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma leftChild_edgeValue_true_eq
  {k : ℤ} :
-- imply
  leftChild (edgeValue (k, true)) = edgeValue (k, false) := by
-- proof
  apply OeisA108081.leftChild_edgeValue_true k

/--
[rightChild_edgeValue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma rightChild_edgeValue_false_eq
  {k : ℤ} :
-- imply
  rightChild (edgeValue (k, false)) = edgeValue (k + 1, true) := by
-- proof
  apply OeisA108081.rightChild_edgeValue_false k

/--
[rightChild_edgeValue_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma rightChild_edgeValue_true_eq
  {k : ℤ} :
-- imply
  rightChild (edgeValue (k, true)) = edgeValue (k - 1, false) := by
-- proof
  apply OeisA108081.rightChild_edgeValue_true k

/--
[map_edgeValue_coordWord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma map_edgeValue_coordWord_eq
  {w : Word} :
-- imply
  (coordWord w).map edgeValue = w := by
-- proof
  apply OeisA108081.map_edgeValue_coordWord w

/--
[coordWord_map_edgeValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma coordWord_map_edgeValue_eq
  {w : List EdgeCoord} :
-- imply
  coordWord (w.map edgeValue) = w := by
-- proof
  apply OeisA108081.coordWord_map_edgeValue w

/--
[edgeValue_coordLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma edgeValue_coordLeft_eq
  {q : EdgeCoord} :
-- imply
  edgeValue (coordLeft q) = leftChild (edgeValue q) := by
-- proof
  apply OeisA108081.edgeValue_coordLeft q

/--
[edgeValue_coordRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma edgeValue_coordRight_eq
  {q : EdgeCoord} :
-- imply
  edgeValue (coordRight q) = rightChild (edgeValue q) := by
-- proof
  apply OeisA108081.edgeValue_coordRight q

/--
[edgeCoord_leftChild](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma edgeCoord_leftChild_eq
  {z : ℤ} :
-- imply
  edgeCoord (leftChild z) = coordLeft (edgeCoord z) := by
-- proof
  apply OeisA108081.edgeCoord_leftChild z

/--
[edgeCoord_rightChild](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma edgeCoord_rightChild_eq
  {z : ℤ} :
-- imply
  edgeCoord (rightChild z) = coordRight (edgeCoord z) := by
-- proof
  apply OeisA108081.edgeCoord_rightChild z

/--
[fst_coordLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma fst_coordLeft_eq
  {q : EdgeCoord} :
-- imply
  (coordLeft q).1 = q.1 := by
-- proof
  apply OeisA108081.fst_coordLeft q

/--
[rightIndex_coordRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma rightIndex_coordRight_eq
  {q : EdgeCoord} :
-- imply
  rightIndex (coordRight q) = rightIndex q := by
-- proof
  apply OeisA108081.rightIndex_coordRight q

/--
[XInsert.base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma base_eq :
-- imply
  XInsert [0] := by
-- proof
  apply OeisA108081.XInsert.base

/--
[bitsToCoords_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma bitsToCoords_cons_eq
  {k : ℤ}
  {e : Bool}
  {b : List Bool} :
-- imply
  bitsToCoords k (e :: b) = (k, e) :: match b with := by
-- proof
  apply OeisA108081.bitsToCoords_cons k e b

/--
[length_subsetBits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma length_subsetBits_eq
  {N : ℕ}
  {s : Finset (Fin N)} :
-- imply
  (subsetBits N s).length = N := by
-- proof
  apply OeisA108081.length_subsetBits N s

/--
[CoordForest.singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma singleton_eq
  {root : EdgeCoord} :
-- imply
  CoordForest root [root] := by
-- proof
  apply OeisA108081.CoordForest.singleton root

/--
[coordLeft_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma coordLeft_ne_eq
  {q : EdgeCoord} :
-- imply
  coordLeft q ≠ q := by
-- proof
  apply OeisA108081.coordLeft_ne q

/--
[coordRight_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma coordRight_ne_eq
  {q : EdgeCoord} :
-- imply
  coordRight q ≠ q := by
-- proof
  apply OeisA108081.coordRight_ne q

/--
[coordLeft_coordLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma coordLeft_coordLeft_eq
  {q : EdgeCoord} :
-- imply
  coordLeft (coordLeft q) = q := by
-- proof
  apply OeisA108081.coordLeft_coordLeft q

/--
[coordRight_coordRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean)
-/
@[path]
private lemma coordRight_coordRight_eq
  {q : EdgeCoord} :
-- imply
  coordRight (coordRight q) = q := by
-- proof
  apply OeisA108081.coordRight_coordRight q


-- created on 2026-10-23
