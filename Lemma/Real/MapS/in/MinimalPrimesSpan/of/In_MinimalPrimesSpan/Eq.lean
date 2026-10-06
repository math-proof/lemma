import Mathlib
import sympy.Basic


/--
[Ideal_map_mem_minimalPrimes_span_singleton_of_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_map_mem_minimalPrimes_span_singleton_of_apply_eq.lean)
-/
@[main]
private lemma main
  [CommRing S]
  {π : S}
  {P : Ideal S}
-- given
  (γ : S ≃+* S)
  (hγπ : γ π = π)
  (hP : P ∈ (Ideal.span {π}).minimalPrimes) :
-- imply
  P.map (γ : S →+* S) ∈ (Ideal.span {π}).minimalPrimes := by
-- proof
  have key : ∀ (e : S ≃+* S), e π = π → ∀ Q ∈ (Ideal.span {π}).minimalPrimes,
      Q.map (e : S →+* S) ∈ (Ideal.span {π}).minimalPrimes := by
    intro e he Q hQ
    have hQp : Q.IsPrime := hQ.1.1
    have hle : Ideal.span {π} ≤ Q := hQ.1.2
    refine ⟨⟨Ideal.map_isPrime_of_equiv e, ?_⟩, ?_⟩
    · rw [Ideal.span_singleton_le_iff_mem, ← he]
      exact Ideal.mem_map_of_mem _ ((Ideal.span_singleton_le_iff_mem _).mp hle)
    · rintro q ⟨hq, hπq⟩ hqle

      have hq' : (q.map ((e.symm : S ≃+* S) : S →+* S)).IsPrime := Ideal.map_isPrime_of_equiv e.symm
      have hπq' : Ideal.span {π} ≤ q.map ((e.symm : S ≃+* S) : S →+* S) := by
        rw [Ideal.span_singleton_le_iff_mem]
        have : e.symm π = π := by rw [← he, RingEquiv.symm_apply_apply, he]
        rw [← this]
        exact Ideal.mem_map_of_mem _ ((Ideal.span_singleton_le_iff_mem _).mp hπq)
      have hq'le : q.map ((e.symm : S ≃+* S) : S →+* S) ≤ Q := by
        have := Ideal.map_mono (f := ((e.symm : S ≃+* S) : S →+* S)) hqle
        rwa [Ideal.map_map, show ((e.symm : S ≃+* S) : S →+* S).comp (e : S →+* S) = RingHom.id S from by
          ext x; simp, Ideal.map_id] at this
      have heq : q.map ((e.symm : S ≃+* S) : S →+* S) = Q := le_antisymm hq'le (hQ.2 ⟨hq', hπq'⟩ hq'le)

      have := congrArg (Ideal.map (e : S →+* S)) heq
      rw [Ideal.map_map, show (e : S →+* S).comp ((e.symm : S ≃+* S) : S →+* S) = RingHom.id S from by
          ext x; simp, Ideal.map_id] at this
      exact this.symm.le
  exact key γ hγπ P hP


-- created on 2026-10-05
