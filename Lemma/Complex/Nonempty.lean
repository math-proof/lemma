import Mathlib
import Initialize.Tactic.Attr.Basic
open Cardinal


/--
[Field_nonempty_ringHom_complex_of_countable](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Field_nonempty_ringHom_complex_of_countable.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K] [CharZero K] [Countable K] :
-- imply
  Nonempty (K →+* ℂ) := by
-- proof
  classical
    have : FaithfulSMul ℚ K :=
      (faithfulSMul_iff_algebraMap_injective ℚ K).2 (algebraMap ℚ K).injective
    have : FaithfulSMul ℚ ℂ :=
      (faithfulSMul_iff_algebraMap_injective ℚ ℂ).2 (algebraMap ℚ ℂ).injective
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
    obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
    have hct : #ℂ = #t :=
      IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' (R := ℚ) _ ht
        mk_le_aleph0 (by simpa [mk_complex] using aleph0_lt_continuum)
    have h1 : Cardinal.lift.{0} #s ≤ Cardinal.lift.{u} #t := by
      rw [← hct, mk_complex, lift_continuum]
      calc
        _ ≤ Cardinal.lift.{0} ℵ₀ := lift_le.2 mk_le_aleph0
        _ = ℵ₀ := lift_aleph0
        _ ≤ 𝔠 := aleph0_le_continuum
    obtain ⟨e⟩ := Cardinal.lift_mk_le'.1 h1
    have hind : AlgebraicIndependent ℚ (fun i : s => ((e i : t) : ℂ)) :=
      ht.1.comp e e.injective
    set A := Algebra.adjoin ℚ (Set.range ((↑) : s → K)) with hA
    let g : A →ₐ[ℚ] ℂ :=
      (MvPolynomial.aeval (fun i : s => ((e i : t) : ℂ))).comp hs.1.aevalEquiv.symm.toAlgHom
    have hg : Function.Injective g :=
      (algebraicIndependent_iff_injective_aeval.1 hind).comp hs.1.aevalEquiv.symm.injective
    have : Algebra.IsAlgebraic A K := hs.isAlgebraic
    let : Algebra A ℂ := g.toRingHom.toAlgebra
    have : Module.IsTorsionFree A ℂ :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr hg
    have : Module.IsTorsionFree A K :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
    exact ⟨(IsAlgClosed.lift (R := A) (S := K) (M := ℂ)).toRingHom⟩


-- created on 2026-10-23
