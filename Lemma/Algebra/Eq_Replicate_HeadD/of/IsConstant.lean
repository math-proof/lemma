import Lemma.Algebra.All_Eq_HeadD.of.IsConstant
import Lemma.Algebra.IsConstantTail.of.IsConstant
import Lemma.Algebra.FunGet_0.of.NeLength_0.All_Fun
import Lemma.Algebra.Eq.of.EqValS
open Algebra


@[main]
private lemma main
  {s : List α}
-- given
  (h: s is constant)
  (default : α) :
-- imply
  s = List.replicate s.length (s.headD default) := by
-- proof
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    have h_tail_is_constant := IsConstantTail.of.IsConstant h
    have h_eq : xs = List.replicate xs.length (xs.headD default) := ih h_tail_is_constant
    simp
    unfold List.replicate
    simp [IsConstant.is_constant] at h
    have h_eq' : List.replicate xs.length (xs.headD default) = List.replicate xs.length x := by
      match xs with
      | .nil =>
        simp
      | .cons y ys =>
        simp
        apply FunGet_0.of.NeLength_0.All_Fun (h_all := h)
        simp
    rw [h_eq'.symm, h_eq.symm]


@[main]
private lemma vector
  {s : List.Vector α n}
-- given
  (h: s is constant)
  (default : α) :
-- imply
  s = List.Vector.replicate n (s.headD default) := by
-- proof
  have h := main h
  have h : s.val = List.replicate s.val.length (s.val.headD default) := h default
  have h_eq_length : s.val.length = s.length := by simp [List.Vector.length]
  have h_eq_headD : s.val.headD default = s.headD default := rfl
  rw [h_eq_length, h_eq_headD] at h
  let vec : List.Vector α n := ⟨
    List.replicate s.length (s.headD default),
    by simp
  ⟩
  have h_eq_vector : List.Vector.replicate s.length (s.headD default) = vec := rfl
  let vec' : List.Vector α n := ⟨
    s.val,
    h_eq_length
  ⟩
  have h_eq_vec : vec.val = vec'.val := by
    rw [h]
  have h_eq_vec: vec = vec' := Eq.of.EqValS h_eq_vec
  have h_eq_s : s = vec' := rfl
  rw [h_eq_vector, h_eq_vec, h_eq_s]


-- created on 2024-07-01
