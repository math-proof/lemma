import Lemma.Vector.Eq.of.EqValS
import Lemma.List.EqReplicate_HeadD.of.IsConstant
import sympy.vector.Basic
open Vector List


@[main, comm]
private lemma main
  {s : List.Vector α n}
-- given
  (h : s is constant)
  (default : α) :
-- imply
  List.Vector.replicate n (s.headD default) = s := by
-- proof
  have h := EqReplicate_HeadD.of.IsConstant h
  have h := h default
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
    rw [← h]
  have h_eq_vec : vec = vec' := Eq.of.EqValS h_eq_vec
  have h_eq_s : s = vec' := rfl
  rw [h_eq_vector, h_eq_vec, h_eq_s]


-- created on 2025-10-03
