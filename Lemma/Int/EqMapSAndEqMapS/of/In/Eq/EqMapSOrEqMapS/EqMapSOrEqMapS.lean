import Mathlib
import sympy.Basic


/--
[Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_map_eq_self_of_apply_eq_of_mem_of_not_mem.lean)
-/
@[path]
private lemma main
  [CommRing S]
  {P₁ P₂ : Ideal S}
  {a : S}
-- given
  (γ : S ≃+* S)
  (h₁ : P₁.map (γ : S →+* S) = P₁ ∨ P₁.map (γ : S →+* S) = P₂)
  (h₂ : P₂.map (γ : S →+* S) = P₁ ∨ P₂.map (γ : S →+* S) = P₂)
  (hγa : γ a = a)
  (ha₁ : a ∈ P₁)
  (ha₂ : a ∉ P₂) :
-- imply
  P₁.map (γ : S →+* S) = P₁ ∧ P₂.map (γ : S →+* S) = P₂ := by
-- proof
  have hmem : a ∈ P₁.map (γ : S →+* S) := by
    rw [← hγa]; exact Ideal.mem_map_of_mem _ ha₁
  have hP₁ : P₁.map (γ : S →+* S) = P₁ := by
    rcases h₁ with h | h
    · exact h
    · exact absurd (h ▸ hmem) ha₂
  refine ⟨hP₁, ?_⟩
  rcases h₂ with h | h
  ·
    exfalso
    have hinj : Function.Injective (Ideal.map (γ : S →+* S)) := fun I J hIJ => by
      have := congrArg (Ideal.map ((γ.symm : S ≃+* S) : S →+* S)) hIJ
      rwa [Ideal.map_map, Ideal.map_map, show ((γ.symm : S ≃+* S) : S →+* S).comp (γ : S →+* S) = RingHom.id S
        from by ext x; simp, Ideal.map_id, Ideal.map_id] at this
    have : P₂ = P₁ := hinj (h.trans hP₁.symm)
    exact ha₂ (this ▸ ha₁)
  · exact h


-- created on 2026-10-05
