import Mathlib
import Lemma.Ideal.Basic
import sympy.Basic

open scoped nonZeroDivisors
open AffineDilatation

/--
[AffineDilatation_isSMulRegular_and_map_eq_span_singleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AffineDilatation_isSMulRegular_and_map_eq_span_singleton.lean)
-/

private lemma isSMulRegular
  {A : Type u}
  [CommRing A]
  (I : Ideal A) (a : A) : IsSMulRegular (Ring I a) a := by
  intro x y hxy
  apply Subtype.ext
  apply (IsLocalization.Away.algebraMap_isUnit a).mul_left_cancel
  have := congrArg (fun z : Ring I a => (z : Localization.Away a)) hxy
  simpa [Algebra.smul_def] using this

private lemma algebraMap_mem_nonZeroDivisors
  {A : Type u}
  [CommRing A]
  (I : Ideal A) (a : A) :
  algebraMap A (Ring I a) a ∈ (Ring I a)⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine isSMulRegular I a (?_ : a • x = a • (0 : Ring I a))
  rwa [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_comm]

private lemma map_eq_span
  {A : Type u}
  [CommRing A]
  (I : Ideal A) (a : A) (ha : a ∈ I) :
  I.map (algebraMap A (Ring I a)) = Ideal.span {algebraMap A (Ring I a) a} := by
  apply le_antisymm
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    exact ⟨divElem I a g hg, by rw [mul_comm, algebraMap_mul_divElem]⟩
  ·
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ha

@[path]
private lemma main
  {A : Type u} [CommRing A]
  {I : Ideal A}
  {a : A}
-- given
  (ha : a ∈ I) :
-- imply
  IsSMulRegular (AffineDilatation.Ring I a) a ∧
      I.map (algebraMap A (AffineDilatation.Ring I a)) =
        Ideal.span {algebraMap A (AffineDilatation.Ring I a) a} :=
-- proof
  ⟨isSMulRegular I a, map_eq_span I a ha⟩

-- created on 2026-10-09
