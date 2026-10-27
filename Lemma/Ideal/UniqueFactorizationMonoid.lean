import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    -- imply
    UniqueFactorizationMonoid A := by
    -- proof
  classical
  have hspan_ne_top : Ideal.span {t} ≠ ⊤ := fun h =>
    zero_ne_one ((Ideal.Quotient.zero_eq_one_iff (I := Ideal.span {t})).mpr h)
  have htm : t ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal hspan_ne_top (Ideal.subset_span (Set.mem_singleton t))
  have hprime_span : (Ideal.span {t}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {t})).mp inferInstance
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun I hI hIp => ?_
  if hA : t ∈ I ∧ t ≠ 0 then
    exact ⟨t, hA.1, (Ideal.span_singleton_prime hA.2).mp hprime_span⟩
  else
    set π := Ideal.Quotient.mk (Ideal.span {t}) with hπ
    obtain ⟨gbar, hgbar⟩ := (IsPrincipalIdealRing.principal (I.map π)).principal
    have hgmem : gbar ∈ I.map π := by rw [hgbar]; apply Ideal.mem_span_singleton_self _
    obtain ⟨f, hfI, hfg⟩ := (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).mp hgmem
    have hle : I ≤ Ideal.span {f} ⊔ Ideal.span {t} • I := by
      intro g hg
      have hπg : π g ∈ I.map π := Ideal.mem_map_of_mem _ hg
      rw [hgbar, ← hfg, Ideal.mem_span_singleton] at hπg
      obtain ⟨cbar, hc⟩ := hπg
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective cbar
      have hdiff : g - f * c ∈ Ideal.span {t} := Ideal.Quotient.eq.mp (by rw [map_mul]; apply hc)
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hdiff
      have hfc : f * c ∈ Ideal.span {f} := Ideal.mem_span_singleton'.mpr ⟨c, mul_comm c f⟩
      obtain htI | ht0 := not_and_or.mp hA
      ·
        have hdI : d ∈ I := by
          apply (hIp.mem_or_mem (by rw [hd]; apply I.sub_mem hg (I.mul_mem_right _ hfI))).resolve_right htI
        have hg' : g = f * c + t * d := by rw [mul_comm t d, hd]; ring
        rw [hg']
        apply Submodule.add_mem_sup hfc (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) hdI)
      ·
        rw [not_ne_iff] at ht0
        have hg' : g = f * c := by rw [← sub_eq_zero, ← hd, ht0, mul_zero]
        rw [hg']
        apply Submodule.mem_sup_left hfc
    have hjac : Ideal.span {t} ≤ (⊥ : Ideal A).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      apply (Ideal.span_singleton_le_iff_mem _).mpr htm
    have hIf : I ≤ Ideal.span {f} :=
      Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hjac hle
    have hIeq : I = Ideal.span {f} := le_antisymm hIf ((Ideal.span_singleton_le_iff_mem _).mpr hfI)
    refine ⟨f, hfI, (Ideal.span_singleton_prime ?_).mp (hIeq ▸ hIp)⟩
    rintro rfl
    apply hI (by rw [hIeq, Ideal.span_singleton_eq_bot])


-- created on 2026-10-20
