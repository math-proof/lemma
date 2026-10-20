/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/ResidueGenerator.lean -/

import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Residue generators

Let `B` be an `A`-algebra and `q` an ideal of `B`. If `B` is generated over `A`
by a single element `π ∈ q`, then the canonical map of residue algebras
`A ⧸ q.comap (algebraMap A B) → B ⧸ q` is surjective: writing an element of `B`
as a polynomial in `π`, only the constant coefficient survives in the quotient,
since `π` itself maps to zero.

## Main results

* `Ideal.quotient_algebraMap_surjective_of_adjoin_singleton_eq_top`: the
  canonical `A`-algebra map on residue algebras is surjective.
* `Ideal.inertiaDeg_eq_one_of_adjoin_singleton_eq_top`: the inertia degree
  is `1` under the same single-generator hypothesis.
-/

namespace Ideal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- If `B` is generated over `A` by an element `π ∈ q`, then the canonical
`A`-algebra map `A ⧸ q.comap (algebraMap A B) → B ⧸ q` is surjective.

Indeed, lift a class to `b : B`, write `b` as `Polynomial.aeval π p`, and use
the constant coefficient `p.coeff 0`: all higher terms vanish in `B ⧸ q`
because `π` maps to zero. -/
theorem quotient_algebraMap_surjective_of_adjoin_singleton_eq_top
    (q : Ideal B) (π : B) (hπ : π ∈ q)
    (hgen : Algebra.adjoin A {π} = ⊤) :
    Function.Surjective (algebraMap (A ⧸ q.comap (algebraMap A B)) (B ⧸ q)) := by
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hb : b ∈ Algebra.adjoin A {π} := by simp [hgen]
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨f, rfl⟩ := hb
  refine ⟨Ideal.Quotient.mk _ (f.coeff 0), ?_⟩
  change algebraMap A (B ⧸ q) (f.coeff 0) = Ideal.Quotient.mk q (f.eval₂ (algebraMap A B) π)
  rw [Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem.mpr hπ, Polynomial.eval₂_at_zero]
  rfl

/-- If `B` is generated over `A` by an element `π ∈ q`, then the inertia
degree of a maximal `q` over a maximal `q.under A` is `1`: the residue
algebras coincide via the surjective canonical map, so the extension has
finite rank one. -/
theorem inertiaDeg_eq_one_of_adjoin_singleton_eq_top
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsMaximal] [(q.under A).IsMaximal]
    (π : B) (hπ : π ∈ q)
    (hgen : Algebra.adjoin A {π} = ⊤) :
    q.inertiaDeg A = 1 := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (q.under A) q]
  exact Module.finrank_of_bijective_algebraMap
    ⟨Ideal.algebraMap_quotient_injective,
      quotient_algebraMap_surjective_of_adjoin_singleton_eq_top q π hπ hgen⟩

end Ideal
