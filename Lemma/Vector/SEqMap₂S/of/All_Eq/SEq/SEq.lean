import Lemma.Bool.SEq.is.Eq
import Lemma.Vector.Eq.is.All_EqGetS
open Bool Vector


@[main]
private lemma main
  {a : List.Vector α n}
  {a' : List.Vector α n'}
  {b : List.Vector β n}
  {b' : List.Vector β n'}
  {f : α → β → γ}
  {f' : α → β → γ}
-- given
  (h_a : a ≃ a')
  (h_b : b ≃ b')
  (h : ∀ i, f (a.get i) (b.get i) = f' (a'.get ⟨i, by rw [← h_a.left]; grind⟩) (b'.get ⟨i, by rw [← h_b.left]; grind⟩)) :
-- imply
  List.Vector.map₂ f a b ≃ List.Vector.map₂ f' a' b' := by
-- proof
  have h_n : n = n' := h_a.left
  subst h_n
  have h_a := Eq.of.SEq h_a
  have h_b := Eq.of.SEq h_b
  subst h_a h_b
  apply SEq.of.Eq
  apply Eq.of.All_EqGetS.fin
  intro i
  simp
  apply h


-- created on 2026-01-11
