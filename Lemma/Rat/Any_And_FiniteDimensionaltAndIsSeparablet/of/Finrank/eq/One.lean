import Mathlib
import sympy.Basic
open IntermediateField


universe u v

/--
[AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [Algebra.Transcendental K F]
-- given
  (hΩ : Module.finrank F Ω[F⁄K] = 1) :
-- imply
  ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
-- proof
  classical
  obtain ⟨t, ht⟩ : ∃ t : F, KaehlerDifferential.D K F t ≠ 0 := by
    by_contra h
    push Not at h
    have htop : (⊤ : Submodule F Ω[F⁄K]) = ⊥ := by
      rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
      rintro _ ⟨x, rfl⟩
      exact h x
    have h0 : Module.finrank F Ω[F⁄K] = 0 := by
      rw [← finrank_top, htop, finrank_bot]
    omega
  have hspan : ∀ ω : Ω[F⁄K], ∃ c : F, c • KaehlerDifferential.D K F t = ω :=
    (finrank_eq_one_iff_of_nonzero' _ ht).mp hΩ
  have hDt : KaehlerDifferential.D K⟮t⟯ F t = 0 := by
    have h := (KaehlerDifferential.D K⟮t⟯ F).map_algebraMap (AdjoinSimple.gen K t)
    rwa [AdjoinSimple.algebraMap_gen] at h
  have hsub : Subsingleton Ω[F⁄K⟮t⟯] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨ω₀, rfl⟩ := KaehlerDifferential.map_surjective K K⟮t⟯ F ω
    obtain ⟨c, rfl⟩ := hspan ω₀
    rw [map_smul, KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply, hDt,
      smul_zero]
  let _ : Algebra.FormallyUnramified K⟮t⟯ F := ⟨hsub⟩
  let _ : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  have hsep : Algebra.IsSeparable K⟮t⟯ F := Algebra.FormallyUnramified.isSeparable K⟮t⟯ F
  have hfin : Module.Finite K⟮t⟯ F := Algebra.FormallyUnramified.finite_of_free K⟮t⟯ F
  refine ⟨t, ?_, hfin, hsep⟩
  show ¬IsAlgebraic K t
  intro halg
  let _ : Algebra.IsAlgebraic K K⟮t⟯ := isAlgebraic_adjoin_simple halg.isIntegral
  let _ : Algebra.IsAlgebraic K⟮t⟯ F := Algebra.IsAlgebraic.of_finite K⟮t⟯ F
  apply Algebra.transcendental_iff_not_isAlgebraic.mp ‹Algebra.Transcendental K F›
  apply Algebra.IsAlgebraic.trans (R := K) (S := K⟮t⟯) (A := F)


-- created on 2026-10-20
