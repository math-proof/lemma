import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[IsDedekindDomain.isPrincipalIdealRing_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/PrincipalIdealQuotient.lean)
-/
@[path]
lemma IsDedekindDomain.isPrincipalIdealRing_quotient
  [CommRing A] [IsDedekindDomain A]
  {I : Ideal A}
-- given
  (hI : I ≠ ⊥) :
-- imply
  IsPrincipalIdealRing (A ⧸ I) where
    principal J := by
-- proof
  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have ha0' : (Ideal.Quotient.mk I) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr haI
  have haJ : a ∈ J.comap (Ideal.Quotient.mk I) := by
    change (Ideal.Quotient.mk I) a ∈ J
    rwa [ha0']
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_eq_span_pair haJ ha0
  have hmap : Ideal.map (Ideal.Quotient.mk I) (J.comap (Ideal.Quotient.mk I)) = J :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective J
  rw [hb, Ideal.map_span] at hmap
  rw [Set.image_pair, ha0', Ideal.span_insert,
    Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq] at hmap
  exact ⟨_, hmap.symm⟩


-- created on 2026-10-20
-- updated on 2026-10-26
