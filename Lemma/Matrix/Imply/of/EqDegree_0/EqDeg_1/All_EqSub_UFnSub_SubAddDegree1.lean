import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.DivisorClassGroup
import Lemma.AlgebraicCurve.Repartitions
import Lemma.AlgebraicCurve.AdelicIndex
import Lemma.Int.P2MUtil

open AlgebraicCurve Module

/--
[AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F] [HasPrincipalDivisors K F]
  {g : ℕ}
  {Kc : Divisor K F}
  {P : Place K F}
  {A : Divisor K F}
-- given
  (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
  (hP : P.deg = 1)
  (hA : Divisor.degree A = 0) :
-- imply
  ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧
      E - (A + (g : ℤ) • Finsupp.single P 1) ∈ Divisor.principal (K :=
  K) (F := F) := by
-- proof
   set D : Divisor K F := A + (g : ℤ) • Finsupp.single P 1 with hD
   have hdeg : Divisor.degree D = g := by
     rw [hD, map_add, map_zsmul, Divisor.degree_single, hA, hP]
     simp
   have hpos : 0 < finrank K (LSpace D) := by
     have h := hRR D
     rw [hdeg] at h
     have h0 : (0 : ℤ) ≤ (ell (Kc - D) : ℤ) := Int.natCast_nonneg _
     have h1 : (1 : ℤ) ≤ (ell D : ℤ) := by linarith
     have h2 : 1 ≤ ell D := by exact_mod_cast h1
     refine h2
   have hne : LSpace D ≠ ⊥ := by
     intro h
     rw [h, finrank_bot] at hpos
     exact lt_irrefl 0 hpos
   obtain ⟨f, hfD, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
   have hord : ∀ v : Place K F, -D v ≤ v.ord f := (mem_lSpace_iff_ord.mp hfD).resolve_left hf0
   obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
   refine ⟨D + Df, fun v => ?_, ?_⟩
   ·
     rw [Finsupp.add_apply, hDf v]
     linarith [hord v]
   ·
     rw [add_sub_cancel_left]
     exact ⟨f, hf0, hDf⟩


-- created on 2026-10-23
