import Lemma.Vector.Eq.of.EqValS
import Lemma.List.Eq_Replicate_HeadD.of.IsConstant
open Vector List


@[main]
private lemma main
  {s : List.Vector α n}
-- given
  (h : s is constant)
  (default : α) :
-- imply
  s = List.Vector.replicate n (s.headD default) := by
-- proof
  have h := Eq_Replicate_HeadD.of.IsConstant h
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
  have h_eq_vec : vec = vec' := Eq.of.EqValS h_eq_vec
  have h_eq_s : s = vec' := rfl
  rw [h_eq_vector, h_eq_vec, h_eq_s]


-- created on 2025-10-03
