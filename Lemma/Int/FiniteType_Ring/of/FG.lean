import Mathlib
import Lemma.Ideal.Basic
import sympy.Basic

open AffineDilatation

/--
[AffineDilatation_finiteType_of_fg](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AffineDilatation_finiteType_of_fg.lean)
-/

private lemma fg_of_fg
  {A : Type v}
  [CommRing A]
  (I : Ideal A) (a : A) (hI : I.FG) : (subalgebra I a).FG := by
  classical
  obtain ⟨T, hT⟩ := hI
  let aa : Submonoid.powers a := ⟨a, Submonoid.mem_powers a⟩
  let f : A → Localization.Away a := fun g => IsLocalization.mk' (Localization.Away a) g aa
  refine ⟨T.image f, le_antisymm ?_ ?_⟩
  ·
    apply Algebra.adjoin_le
    intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact gen_subset I a ⟨g, hT ▸ Ideal.subset_span hg, rfl⟩
  ·
    apply Algebra.adjoin_le
    rintro x ⟨g, hg, rfl⟩
    have hg' : g ∈ Ideal.span (T : Set A) := hT ▸ hg
    clear hg
    change f g ∈ Algebra.adjoin A (↑(T.image f) : Set (Localization.Away a))
    have hu : ∀ g : A, f g = algebraMap A (Localization.Away a) g * f 1 := fun g =>
      IsLocalization.mk'_eq_mul_mk'_one g aa
    rw [hu]
    induction hg' using Submodule.span_induction with
    | mem t ht =>
      rw [← hu]
      exact Algebra.subset_adjoin (by rw [Finset.coe_image]; exact ⟨t, ht, rfl⟩)
    | zero =>
      rw [map_zero, zero_mul]
      exact Subalgebra.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add, add_mul]
      exact Subalgebra.add_mem _ hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, map_mul, mul_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) hx

private lemma finiteType
  {A : Type v}
  [CommRing A]
  (I : Ideal A) (a : A) (hI : I.FG) : Algebra.FiniteType A (Ring I a) :=
  (Subalgebra.fg_iff_finiteType _).mp (fg_of_fg I a hI)
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  {I : Ideal A}
  {a : A}
-- given
  (hI : I.FG) :
-- imply
  Algebra.FiniteType R (AffineDilatation.Ring I a) :=
-- proof
  Algebra.FiniteType.trans (S := A) inferInstance
    (finiteType I a hI)


-- created on 2026-10-09
