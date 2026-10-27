import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraNotes.code.CommutativeAlgebra
open MvPolynomial Ideal CommutativeAlgebra


namespace CommutativeAlgebra

/--
[hilbert_nullstellensatz_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/CommutativeAlgebra.lean)
-/
@[path]
lemma hilbert_nullstellensatz_base
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) ℂ)} :
-- imply
  I.IsMaximal ↔ ∃ a : Fin n → ℂ, I = vanishingIdeal ℂ {a} :=
-- proof
  MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton

end CommutativeAlgebra

namespace CommutativeAlgebra

/--
[vanishingIdeal_singleton_eq_ker_aeval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/CommutativeAlgebra.lean)
-/
@[path]
lemma vanishingIdeal_singleton_eq_ker_aeval
  {n : ℕ}
  {a : Fin n → ℂ} :
-- imply
  (vanishingIdeal ℂ {a} : Ideal (MvPolynomial (Fin n) ℂ)) = RingHom.ker (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) := by
-- proof
  ext p
  simp [RingHom.mem_ker]

end CommutativeAlgebra

namespace CommutativeAlgebra

/--
[hilbert_nullstellensatz_weak_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/CommutativeAlgebra.lean)
-/
@[path]
lemma hilbert_nullstellensatz_weak_ker
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) ℂ)} :
-- imply
  I.IsMaximal ↔ ∃ a : Fin n → ℂ, I = RingHom.ker (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) := by
-- proof
  rw [hilbert_nullstellensatz_base]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.trans (vanishingIdeal_singleton_eq_ker_aeval n a)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ha.trans (vanishingIdeal_singleton_eq_ker_aeval n a).symm⟩

end CommutativeAlgebra

namespace CommutativeAlgebra

/--
[hilbert_nullstellensatz_weak](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/CommutativeAlgebra.lean)
-/
@[path]
lemma hilbert_nullstellensatz_weak
  {n m : ℕ}
  {P : Fin m → MvPolynomial (Fin n) ℂ}
  {J : Ideal (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range P))} :
-- imply
  J.IsMaximal ↔ ∃ a : Fin n → ℂ, (∀ i, MvPolynomial.aeval a (P i) = 0) ∧ J = Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range P))) (vanishingIdeal ℂ {a}) := by
-- proof
  constructor
  · intro hJ
    haveI : J.IsMaximal := hJ
    have hcomap : (Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range P))) J).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨a, ha⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hcomap
    refine ⟨a, ?_, ?_⟩
    · intro i
      have hPi : P i ∈ Ideal.span (Set.range P) := Ideal.subset_span ⟨i, rfl⟩
      have hle : Ideal.span (Set.range P) ≤
        Ideal.comap (Ideal.Quotient.mk (Ideal.span (Set.range P))) J := by
        intro x hx
        rw [Ideal.mem_comap]
        rwa [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      have hPiV : P i ∈ vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := ha ▸ hle hPi
      simp [vanishingIdeal] at hPiV
      exact hPiV
    · have := (Ideal.map_comap_of_surjective (Ideal.Quotient.mk (Ideal.span (Set.range P)))
      Ideal.Quotient.mk_surjective J).symm
      rwa [ha] at this
  · rintro ⟨a, ha, rfl⟩
    have hmax : (vanishingIdeal ℂ ({a} : Set (Fin n → ℂ))).IsMaximal :=
      MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mpr ⟨a, rfl⟩
    have hle : Ideal.span (Set.range P) ≤ vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := by
      rw [Ideal.span_le]
      intro p ⟨i, hi⟩
      simp [vanishingIdeal]
      rw [← hi]
      exact ha i
    haveI := hmax
    have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span (Set.range P))) ≤
      vanishingIdeal ℂ ({a} : Set (Fin n → ℂ)) := by
      rwa [Ideal.mk_ker]
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker

end CommutativeAlgebra


-- created on 2026-10-23
