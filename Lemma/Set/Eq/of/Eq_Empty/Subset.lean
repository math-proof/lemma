import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  {A B C : Set α}
-- given
  (h : B ∩ C = ∅)
  (hs : A ⊆ B) :
-- imply
  C \ A = C := by
-- proof
  ext z
  simp only [Set.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro hc
    have hna : z ∉ A := by
      intro hza
      have hzb : z ∈ B := hs hza
      have : z ∈ B ∩ C := ⟨hzb, hc⟩
      rw [h] at this
      exact this.elim
    exact ⟨hc, hna⟩


-- created on 2021-05-15
