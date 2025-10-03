import sympy.vector.vector
import Lemma.List.Eq_Nil.of.EqLength_0
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.Algebra.EqAddS.is.Eq
import Lemma.List.MapCons.eq.Cons_Map
import Lemma.List.FlattenCons.eq.Append_Flatten
import Lemma.List.Eq.of.EqAppendS.EqLengthS
import Lemma.Vector.Eq.of.EqToListS
open Algebra List Vector


@[main]
private lemma main
  {a b : List (List.Vector α n)}
-- given
  (h₀ : a.length = b.length)
  (h₁ : (a.map List.Vector.toList).flatten = (b.map List.Vector.toList).flatten) :
-- imply
  a = b := by
-- proof
  induction a generalizing b with
  | nil =>
    simp at h₀
    have hb := Eq_Nil.of.EqLength_0 h₀.symm
    exact hb.symm
  | cons a₀ a ih =>
    match b with
    | [] =>
      contradiction
    | b₀ :: b =>
      rw [LengthCons.eq.Add1Length, LengthCons.eq.Add1Length] at h₀
      have h₀ := Eq.of.EqAddS.left h₀
      rw [MapCons.eq.Cons_Map, MapCons.eq.Cons_Map] at h₁
      rw [FlattenCons.eq.Append_Flatten, FlattenCons.eq.Append_Flatten] at h₁
      have h_head_length : a₀.toList.length = b₀.toList.length := by
        simp
      have h_head := Eq.of.EqAppendS.EqLengthS h_head_length h₁
      have h_head := Eq.of.EqToListS h_head
      have h₁ := Eq.of.EqAppendS.EqLengthS.drop h_head_length h₁
      have ih := ih (b := b) h₀ h₁
      aesop


-- created on 2025-05-11
