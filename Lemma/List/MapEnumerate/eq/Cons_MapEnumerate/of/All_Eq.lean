import stdlib.List
import Lemma.Nat.LtAddS.is.Lt
import Lemma.List.Eq.of.GetElemRange.eq.Some
import Lemma.List.GetElemEnumerate.eq.Some.of.Lt_length
import Lemma.Algebra.EqMod.of.Lt
import Lemma.Algebra.Eq.of.EqValS
import Lemma.Algebra.Cast_1.eq.One
open Algebra List Nat


@[main]
private lemma main
  {tail : List α}
  {f : Fin (tail.length + 1) × α → β}
  {g : Fin tail.length × α → β}
-- given
  (h : ∀ (i : Fin tail.length) (a : α), f ⟨⟨i + 1, by apply LtAddS.of.Lt; simp_all⟩, a⟩ = g ⟨i, a⟩)
  (head : α) :
-- imply
  (head :: tail).enumerate.map f = f ⟨0, head⟩ :: tail.enumerate.map g := by
-- proof
  ext i c
  match h_match : i with
  | 0 =>
    simp_all
    constructor
    ·
      intro hi
      let ⟨i, b, hi, hc⟩ := hi
      simp [List.enumerate] at hi
      let ⟨hi, hb⟩ := hi
      rwa [hi, hb]
    ·
      intro hi
      use 0, head
      constructor
      ·
        simp [List.enumerate]
      ·
        assumption
  | .succ i' =>
    simp_all
    constructor
    ·
      intro hi
      let ⟨i, b, hi, hc⟩ := hi
      simp [List.enumerate] at hi
      let ⟨i, h_succ, _, hi, hb⟩ := hi
      have h_succ := Eq.of.GetElemRange.eq.Some h_succ
      have hi' : i' < tail.length := by
        simp_all
        linarith
      use ⟨i', hi'⟩, tail[i']
      have h := h ⟨i', hi'⟩ tail[i']
      constructor
      ·
        rw [GetElemEnumerate.eq.Some.of.Lt_length]
      ·
        rw [← hc]
        rw [hi]
        rw [hb]
        simp [← h_succ]
        simp_all
    ·
      intro hi
      let ⟨i', b, hi, hc⟩ := hi
      simp [List.enumerate] at hi
      let ⟨i, h_some, h_lt, hi, hb⟩ := hi
      have h := h i' tail[i']
      use ⟨i, by omega⟩ + 1, tail[i]
      constructor
      ·
        simp [Eq.of.GetElemRange.eq.Some h_some]
        have : i + 1 < (head :: tail).length := by
          simp_all
        have := GetElemEnumerate.eq.Some.of.Lt_length this
        simp_all
        congr
        simp
        have h_lt : i + 1 < tail.length + 1 := by
          simp_all
        rw [EqMod.of.Lt h_lt]
      ·
        rw [← hc]
        simp [hi]
        simp [← hb]
        rw [hi] at h
        simp at h
        rw [← hb] at h
        simp_all
        rw [← h]
        congr
        apply Eq.of.EqValS
        simp [HAdd.hAdd]
        simp [Add.add]
        simp [Fin.add]
        simp_all


-- created on 2025-06-02
-- updated on 2025-06-08
