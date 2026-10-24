import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GaloisRep_LocalConditions
import Lemma.Definitions.Def_GaloisRep_Residual
import Lemma.Int.P2MUtil

open IsLocalRing

/--
[GaloisRepAdic_ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_ordinaryLine_eq_and_frobeniusScalar_eq_of_exists_inertia_ne_one.lean)
-/
@[path]
private lemma main
  [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪]
  {ρ' : GaloisRepAdic 𝒪}
  {p : ℕ}
  {P : ValuationSubring (AlgebraicClosure ℚ)}
  {L : Submodule 𝒪 ρ'.V}
  {α : 𝒪}
  {L' : Submodule 𝒪 ρ'.V}
  {α' : 𝒪}
-- given
  (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 ρ'.V, L = 𝒪 ∙ b 0)
  (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ'.V, ρ'.ρ σ v - v ∈ L)
  (hα : ∀ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p → ∀ v : ρ'.V, ρ'.ρ σ v - α • v ∈ L)
  (hL'b : ∃ b : Module.Basis (Fin 2) 𝒪 ρ'.V, L' = 𝒪 ∙ b 0)
  (hL'I : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ'.V, ρ'.ρ τ v - v ∈ L')
  (hα' : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p → ∀ v : ρ'.V, ρ'.ρ σ v - α' • v ∈ L')
  (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ'.ρ τ ≠ 1) :
-- imply
  L = L' ∧
      ((∃ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p) → α = α') := by
-- proof
  classical
  obtain ⟨b, rfl⟩ := hLb
  obtain ⟨b', rfl⟩ := hL'b

  set x : 𝒪 := b.repr (b' 0) 0 with hx
  set y : 𝒪 := b.repr (b' 0) 1 with hy
  have hb'0 : b' 0 = x • b 0 + y • b 1 := by
    have h := b.sum_repr (b' 0)
    rw [Fin.sum_univ_two] at h
    exact h.symm

  have coord1 : ∀ {v : ρ'.V}, v ∈ 𝒪 ∙ b 0 → b.repr v 1 = 0 := by
    intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, if_neg (by decide), smul_zero]

  have hLL : (𝒪 ∙ b 0) = (𝒪 ∙ b' 0) := by
    by_cases hy0 : y = 0
    ·
      have hb'0' : b' 0 = x • b 0 := by rw [hb'0, hy0, zero_smul, add_zero]
      have hxu : IsUnit x := by
        have h1 : b'.repr (b' 0) 0 = 1 := by rw [b'.repr_self, Finsupp.single_eq_same]
        rw [hb'0', map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
        exact IsUnit.of_mul_eq_one _ h1
      rw [hb'0', Submodule.span_singleton_smul_eq hxu]
    ·
      exfalso
      obtain ⟨τ, hτ, hτne⟩ := hram
      apply hτne
      ext v
      have h1 := hLI τ hτ v
      have h2 := hL'I τ hτ v

      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h2
      have hc1 : b.repr (ρ'.ρ τ v - v) 1 = c * y := by
        rw [← hc, hb'0, smul_add, smul_smul, smul_smul, map_add, map_smul, map_smul, Finsupp.add_apply,
          Finsupp.smul_apply, Finsupp.smul_apply, b.repr_self, b.repr_self, Finsupp.single_apply, Finsupp.single_apply,
          if_neg (by decide), if_pos rfl, smul_zero, zero_add, smul_eq_mul, mul_one]
      have hc0 : c = 0 := by
        have : c * y = 0 := by rw [← hc1, coord1 h1]
        exact (mul_eq_zero.mp this).resolve_right hy0
      have hw : ρ'.ρ τ v - v = 0 := by rw [← hc, hc0, zero_smul]
      rw [Module.End.one_apply]
      exact sub_eq_zero.mp hw
  refine ⟨hLL, ?_⟩

  rintro ⟨σ, hσD, hσF⟩
  have h1 := hα σ hσD hσF (b 1)
  have h2 := hα' σ hσF (b 1)
  rw [← hLL] at h2
  have h3 : (α' - α) • b 1 ∈ 𝒪 ∙ b 0 := by
    have := Submodule.sub_mem _ h1 h2
    rwa [sub_sub_sub_cancel_left, ← sub_smul] at this
  have h4 := coord1 h3
  rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h4
  exact (sub_eq_zero.mp h4).symm


-- created on 2026-10-23
