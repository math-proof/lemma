import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.DivisorClassGroup
open AlgebraicCurve


/--
[AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {V₀ : Place K F}
  {x : Pic0 K F}
-- given
  (hdeg1 : ∀ v : Place K F, v.deg = 1) :
-- imply
  x ∈ AddSubgroup.closure
    {y : Pic0 K F | ∃ (V : Place K F) (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)), y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} := by
-- proof
    classical
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    have hgen : ∀ v : Place K F,
        Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F) := fun v => by
      rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]; simp
    set g : Place K F → ↥(Divisor.degZero (K := K) (F := F)) := fun v => ⟨_, hgen v⟩ with hg
    have hdeg : ∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v = 0 := by
      have h0 : Divisor.degree (D : Divisor K F) = 0 := Divisor.mem_degZero.mp D.2
      have : Divisor.degree (D : Divisor K F) = ∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v * ((v.deg : ℕ) : ℤ) := by
        show Finsupp.liftAddHom _ (D : Divisor K F) = _
        rw [Finsupp.liftAddHom_apply, Finsupp.sum]
        rfl
      rw [this] at h0
      simpa [hdeg1] using h0
    have hD : D = ∑ v ∈ (D : Divisor K F).support, ((D : Divisor K F) v) • g v := by
      apply Subtype.ext
      rw [AddSubgroup.val_finsetSum]
      simp only [AddSubgroupClass.coe_zsmul, hg, smul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_smul, hdeg, zero_smul, sub_zero]
      simp only [Finsupp.smul_single_one]
      exact ((D : Divisor K F).sum_single).symm
    have hφ : ∀ E, Pic0.mk (K := K) (F := F) E =
        QuotientAddGroup.mk' ((Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))) E :=
      fun E => rfl
    have hmem : ∀ v : Place K F, Pic0.mk (g v) ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F) (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)), y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} :=
      fun v => AddSubgroup.subset_closure ⟨v, hgen v, rfl⟩
    rw [hD, hφ, map_sum]
    refine AddSubgroup.sum_mem _ fun v _ => ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (hmem v) _


-- created on 2026-10-23
