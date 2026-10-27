import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Ideal

/--
[quotient_algebraMap_surjective_of_adjoin_singleton_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/ResidueGenerator.lean)
-/
@[path]
lemma quotient_algebraMap_surjective_of_adjoin_singleton_eq_top
  [CommRing A] [CommRing B] [Algebra A B]
  {q : Ideal B}
  {π : B}
-- given
  (hπ : π ∈ q)
  (hgen : Algebra.adjoin A {π} = ⊤) :
-- imply
  Function.Surjective (algebraMap (A ⧸ q.comap (algebraMap A B)) (B ⧸ q)) := by
-- proof
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hb : b ∈ Algebra.adjoin A {π} := by simp [hgen]
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨f, rfl⟩ := hb
  refine ⟨Ideal.Quotient.mk _ (f.coeff 0), ?_⟩
  change algebraMap A (B ⧸ q) (f.coeff 0) = Ideal.Quotient.mk q (f.eval₂ (algebraMap A B) π)
  rw [Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem.mpr hπ, Polynomial.eval₂_at_zero]
  rfl

end Ideal

namespace Ideal

/--
[inertiaDeg_eq_one_of_adjoin_singleton_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/ResidueGenerator.lean)
-/
@[path]
lemma inertiaDeg_eq_one_of_adjoin_singleton_eq_top
  [CommRing A] [CommRing B] [Algebra A B]
  {q : Ideal B} [q.IsMaximal] [(q.under A).IsMaximal]
  {π : B}
-- given
  (hπ : π ∈ q)
  (hgen : Algebra.adjoin A {π} = ⊤) :
-- imply
  q.inertiaDeg A = 1 := by
-- proof
  rwa [Ideal.inertiaDeg_eq_of_isMaximal (q.under A) q]
    ⟨Ideal.algebraMap_quotient_injective,
      quotient_algebraMap_surjective_of_adjoin_singleton_eq_top q π hπ hgen⟩

end Ideal


-- created on 2026-10-20
-- updated on 2026-10-26
