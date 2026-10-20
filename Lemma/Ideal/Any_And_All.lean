import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem.lean)
-/
@[path]
private lemma main
  {B : Type u} [CommRing B] (P : B → Prop)
  (hloc : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∃ f : B, f ∉ 𝔭 ∧ P f) :
  -- imply
  ∃ (ι : Type u) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧ ∀ i : ι, P (f i) := by
  -- proof
  classical
  have htop : Ideal.span {f : B | P f} = ⊤ := by
    by_contra h
    obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf𝔪, hPf⟩ := hloc 𝔪 h𝔪.isPrime
    apply hf𝔪 (hle (Ideal.subset_span hPf))
  have h1 : (1 : B) ∈ Ideal.span {f : B | P f} := by
    rw [htop]
    apply Submodule.mem_top
  obtain ⟨T, hTsub, h1T⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨↥T, inferInstance, fun t => t.1, ?_, fun t => hTsub t.2⟩
  rw [Ideal.eq_top_iff_one]
  have : Set.range (fun t : ↥T => (t.1 : B)) = (T : Set B) := by
    ext b
    simp
  rw [this]
  apply h1T


-- created on 2026-10-20
