/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part26
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem ZagOddMarks.length_toList {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root : Fin n}
    (m : ZagOddMarks e π root) :
    m.toList.length = 2 * m.depth + 3 := by
  induction m with
  | terminal => rfl
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      simp only [toList, List.length_cons, depth, ih]
      omega

theorem ZagOddMarks.heq_of_toList {n : ℕ}
    {e π : Equiv.Perm (Fin n)} {root root' : Fin n}
    (m : ZagOddMarks e π root) (m' : ZagOddMarks e π root')
    (h : m.toList = m'.toList) : HEq m m' := by
  induction m generalizing root' with
  | terminal a =>
      cases m' with
      | terminal b =>
          simp only [toList, List.cons.injEq] at h
          obtain ⟨hfirst, hmiddle, hthird, _⟩ := h
          have hab : a = b := zagMarkedTriple_ext hfirst hmiddle hthird
          subst b
          rfl
      | prepend _ middle third first_mem middle_mem first_lt_middle
          middle_lt_third tail =>
          have hlen := congrArg List.length h
          rw [length_toList, length_toList] at hlen
          simp only [depth] at hlen
          omega
  | prepend first middle third first_mem middle_mem first_lt_middle
      middle_lt_third tail ih =>
      cases m' with
      | terminal b =>
          have hlen := congrArg List.length h
          rw [length_toList, length_toList] at hlen
          simp only [depth] at hlen
          omega
      | prepend _ middle' third' first_mem' middle_mem' first_lt_middle'
          middle_lt_third' tail' =>
          simp only [toList, List.cons.injEq] at h
          obtain ⟨hfirst, hmiddle, htail⟩ := h
          have hthird : third = third' := by
            have hhead := congrArg List.head? htail
            rw [tail.head?_toList, tail'.head?_toList] at hhead
            exact Option.some.inj hhead
          subst root'
          subst middle'
          subst third'
          have htail_eq : HEq tail tail' := ih tail' htail
          cases htail_eq
          rfl

theorem zagOddMarks_exists_of_list {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (l : List (Fin n))
    (hsorted : l.SortedLT)
    (hmem : ∀ x ∈ l, x ∈ zagCycleMinima e π)
    (hodd : Odd l.length) (hthree : 3 ≤ l.length) :
    ∃ root, ∃ m : ZagOddMarks e π root, m.toList = l := by
  induction l using List.twoStepInduction with
  | nil => simp at hthree
  | singleton a => simp at hthree
  | cons_cons a b l ih _ =>
      rw [List.sortedLT_iff_pairwise] at hsorted
      simp only [List.pairwise_cons] at hsorted
      have hab : a < b := hsorted.1 b (by simp)
      have hsorted_l : l.SortedLT := by
        rw [List.sortedLT_iff_pairwise]
        exact hsorted.2.2
      have hmem_l : ∀ x ∈ l, x ∈ zagCycleMinima e π := by
        intro x hx
        exact hmem x (by simp [hx])
      have hodd_l : Odd l.length := by
        obtain ⟨d, hd⟩ := hodd
        refine ⟨d - 1, ?_⟩
        simp only [List.length_cons] at hd
        omega
      cases l with
      | nil => simp at hodd_l
      | cons c rest =>
          have hbc : b < c := hsorted.2.1 c (by simp)
          cases rest with
          | nil =>
              let m : ZagMarkedTriple e π := {
                first := a
                middle := b
                third := c
                first_mem := hmem a (by simp)
                middle_mem := hmem b (by simp)
                third_mem := hmem c (by simp)
                first_lt_middle := hab
                middle_lt_third := hbc
              }
              exact ⟨a, .terminal m, rfl⟩
          | cons d rest =>
              have hthree_l : 3 ≤ (c :: d :: rest).length := by
                obtain ⟨t, ht⟩ := hodd_l
                simp only [List.length_cons] at ht ⊢
                omega
              obtain ⟨root, tail, htail⟩ :=
                ih hsorted_l hmem_l hodd_l hthree_l
              have hroot : root = c := by
                have hhead := tail.head?_toList
                rw [htail] at hhead
                exact Option.some.inj hhead.symm
              subst root
              refine ⟨a, .prepend a b c (hmem a (by simp))
                (hmem b (by simp)) hab hbc tail, ?_⟩
              simp only [ZagOddMarks.toList, htail]

theorem zagOddMarksSigma_ext {n : ℕ}
    {e π : Equiv.Perm (Fin n)}
    {q q' : Σ root, ZagOddMarks e π root}
    (h : q.2.toList = q'.2.toList) : q = q' := by
  have hroot : q.1 = q'.1 := by
    have hhead := congrArg List.head? h
    rw [q.2.head?_toList, q'.2.head?_toList] at hhead
    exact Option.some.inj hhead
  rcases q with ⟨root, m⟩
  rcases q' with ⟨root', m'⟩
  dsimp only at hroot h ⊢
  subst root'
  have hm : HEq m m' := ZagOddMarks.heq_of_toList m m' h
  cases hm
  rfl

end MetaMathlibExt
