import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.HeckeGalois_EichlerShimura
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_exists_sub_C_mem_eisensteinIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_sub_C_mem_eisensteinIdeal.lean)
-/

private lemma  exists_sub_C_mem_eisensteinIdeal (N : ℕ) (t : HeckeAlg) :
  ∃ n : ℤ, t - MvPolynomial.C n ∈ eisensteinIdeal N := by
  refine ⟨MvPolynomial.aeval (eisensteinSystem N) t, ?_⟩
  rw [eisensteinIdeal, mem_eigenIdeal_iff, map_sub, MvPolynomial.aeval_C]
  simp

private lemma  surjective_algebraMap_quotient_eisensteinIdeal (N : ℕ) :
  Function.Surjective (algebraMap ℤ (HeckeAlg ⧸ eisensteinIdeal N)) := by
  intro x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := exists_sub_C_mem_eisensteinIdeal N t
  refine ⟨n, ?_⟩
  rw [IsScalarTower.algebraMap_apply ℤ HeckeAlg (HeckeAlg ⧸ eisensteinIdeal N), MvPolynomial.algebraMap_eq,
    Ideal.Quotient.algebraMap_eq]
  exact (Ideal.Quotient.eq.mpr hn).symm
@[path]
private lemma main
  {N : ℕ}
  {t : HeckeAlg} :
-- imply
  ∃ n : ℤ, t - MvPolynomial.C n ∈ eisensteinIdeal N :=
  exists_sub_C_mem_eisensteinIdeal N t


-- created on 2026-10-23
