import Mathlib
import sympy.Basic


/--
[Module_isClosed_setOf_range_le_smul_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_isClosed_setOf_range_le_smul_top.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
  {f : P →ₗ[R] Q}
-- given
  (h : Module.Projective R Q) :
-- imply
  IsClosed {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} := by
-- proof
  classical
  let s : Set R := {r | ∃ (φ : Q →ₗ[R] R) (p : P), r = φ (f p)}
  suffices h : {x : PrimeSpectrum R | LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)} = PrimeSpectrum.zeroLocus s by
    rw [h]; exact PrimeSpectrum.isClosed_zeroLocus s
  obtain ⟨sec, hsec⟩ := h.out
  ext x
  simp only [Set.mem_ofPred_eq, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro hx
    rintro r ⟨φ, p, rfl⟩
    have hfp : f p ∈ x.asIdeal • (⊤ : Submodule R Q) := hx ⟨p, rfl⟩
    show φ (f p) ∈ x.asIdeal
    refine Submodule.smul_induction_on (p := fun q => φ q ∈ x.asIdeal) hfp ?_ ?_
    · intro a ha q _
      rw [map_smul, smul_eq_mul]; exact Ideal.mul_mem_right _ _ ha
    · intro u v hu hv
      rw [map_add]; exact Ideal.add_mem _ hu hv
  · intro hx
    rintro _ ⟨p, rfl⟩
    rw [← hsec (f p), Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact hx ⟨(Finsupp.lapply q).comp sec, p, rfl⟩


-- created on 2026-10-05
