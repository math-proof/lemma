module

public import Mathlib
public import Theorem.Nat.LtAddS.is.Lt
public import Theorem.List.Eq.of.GetElemRange.eq.Some
public import Theorem.List.GetElemEnumerate.eq.Some.of.GtLength
public import Theorem.Nat.EqMod.of.Lt
public import Theorem.Fin.Eq.of.Val
public import Theorem.Nat.EqCast_1'1
public section

open List Nat Fin Set


public theorem List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
  {tail : List α}
  {f : Fin (tail.length + 1) × α → β}
  {g : Fin tail.length × α → β}
-- given
  (h : ∀ (i : Fin tail.length) (a : α), f ⟨⟨i + 1, by exact Nat.add_lt_add_right i.isLt 1⟩, a⟩ = g ⟨i, a⟩)
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
        rw [GetElemEnumerate.eq.Some.of.GtLength]
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
        have h_lt : i + 1 < (head :: tail).length := by
          simp_all
        have h_enum := GetElemEnumerate.eq.Some.of.GtLength h_lt
        refine h_enum.trans ?_
        simp
        congr
        have h_lt : i + 1 < tail.length + 1 := by simp_all
        simp [EqMod.of.Lt h_lt]
      ·
        rw [← hc]
        simp [hi]
        simp [← hb]
        simp at h
        simp_all
        rw [← h]
        congr
        apply Eq.of.Val
        simp [HAdd.hAdd]
        simp [Add.add]
        simp [Fin.add]
        simp_all


-- created on 2025-06-02
-- updated on 2025-06-08
