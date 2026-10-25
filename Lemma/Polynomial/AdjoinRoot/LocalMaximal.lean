import Mathlib
import sympy.Basic
import Theorem.RingTheory.AdjoinRoot.LocalMaximal
open Polynomial
open AdjoinRoot


namespace AdjoinRoot

/--
[exists_irreducible_factor_of_is_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean)
-/
@[path]
lemma exists_irreducible_factor_of_is_maximal
  [CommRing A] [IsLocalRing A]
  {g : A[X]} [Algebra.IsIntegral A (AdjoinRoot g)]
  {m : Ideal (AdjoinRoot g)} [hm : m.IsMaximal] :
-- imply
  ∃ q : A[X],
    Irreducible (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧
    (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣
    (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧
    m = Ideal.map (algebraMap A (AdjoinRoot g))
    (IsLocalRing.maximalIdeal A) ⊔
    Ideal.span {AdjoinRoot.mk g q} := by
-- proof
  have hcomap_max : (m.comap (algebraMap A (AdjoinRoot g))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A (AdjoinRoot g))
      (algebraMap_isIntegral_iff.mpr inferInstance) m
  have hcomap_eq : m.comap (algebraMap A (AdjoinRoot g)) =
    IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hcomap_max
  have hle : Ideal.map (algebraMap A (AdjoinRoot g))
    (IsLocalRing.maximalIdeal A) ≤ m := by
    rwa [← hcomap_eq]
  have hsurj : Function.Surjective (Polynomial.mapRingHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) := by
    rw [Polynomial.coe_mapRingHom]
    exact Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  let MM : Ideal A[X] := Ideal.comap (AdjoinRoot.mk g) m
  have hMM_max : MM.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ AdjoinRoot.mk_surjective
  have hker_mk : RingHom.ker (AdjoinRoot.mk g) ≤ MM := fun f hf =>
    show (AdjoinRoot.mk g) f ∈ m from (RingHom.mem_ker.mp hf) ▸ m.zero_mem
  have hCp_le : Ideal.map Polynomial.C (IsLocalRing.maximalIdeal A) ≤ MM := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact hle (Ideal.mem_map_of_mem _ ha)
  have hker_map : Ideal.comap (Polynomial.mapRingHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ⊥ ≤ MM := by
    rwa [Polynomial.comap_mapRingHom_bot_eq_map_C_ker]
  have hMMbar_max : (Ideal.map (Polynomial.mapRingHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) MM).IsMaximal := by
    have := hMM_max
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj
    rwa [RingHom.ker_eq_comap_bot]
  have hg_in : g ∈ MM :=
    hker_mk (by rw [RingHom.mem_ker]; exact AdjoinRoot.mk_self)
  have hgbar_in : Polynomial.map
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) g ∈
    Ideal.map (Polynomial.mapRingHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) MM :=
    Ideal.mem_map_of_mem _ hg_in
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) :=
    Ideal.Quotient.field _
  obtain ⟨qb, hqb⟩ := IsPrincipalIdealRing.principal (Ideal.map
    (Polynomial.mapRingHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
    MM)
  have hMMbar_eq : Ideal.map (Polynomial.mapRingHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) MM =
    Ideal.span {qb} := hqb
  have hqb_irred : Irreducible qb := by
    have hmax : (Ideal.span {qb}).IsMaximal := hMMbar_eq ▸ hMMbar_max
    have hqb0 : qb ≠ 0 := by
      intro h
      subst h
      exact Ring.ne_bot_of_isMaximal_of_not_isField hmax
        (Polynomial.not_isField (A ⧸ IsLocalRing.maximalIdeal A))
        Ideal.span_singleton_zero
    exact ((Ideal.span_singleton_prime hqb0).mp hmax.isPrime).irreducible
  have hqb_dvd : qb ∣ Polynomial.map
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) g := by
    rwa [← Ideal.mem_span_singleton, ← hMMbar_eq]
  obtain ⟨q, hq_lift⟩ := Polynomial.map_surjective
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
    Ideal.Quotient.mk_surjective qb
  have hMM_comap : MM = Ideal.comap (Polynomial.mapRingHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
    (Ideal.map (Polynomial.mapRingHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) MM) := by
    rw [Ideal.comap_map_of_surjective _ hsurj]
    exact (sup_eq_left.mpr hker_map).symm
  have hMMbar_span : Ideal.map (Polynomial.mapRingHom
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) MM =
    Ideal.map (Polynomial.mapRingHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))
      (Ideal.span {q}) := by
    rw [hMMbar_eq, Ideal.map_span, Set.image_singleton]
    simp only [Polynomial.coe_mapRingHom, hq_lift]
  have hMM_decomp : MM = Ideal.span {q} ⊔
    Ideal.map Polynomial.C (IsLocalRing.maximalIdeal A) := by
    rw [hMM_comap, hMMbar_span, Ideal.comap_map_of_surjective _ hsurj,
      Polynomial.comap_mapRingHom_bot_eq_map_C_ker]
  have hmm_map : m = Ideal.map (AdjoinRoot.mk g) MM :=
    (Ideal.map_comap_of_surjective _ AdjoinRoot.mk_surjective m).symm
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [hq_lift]
    exact hqb_irred
  · rw [hq_lift]
    exact hqb_dvd
  · rw [hmm_map, hMM_decomp, Ideal.map_sup, Ideal.map_span,
    Set.image_singleton, Ideal.map_map,
    show (AdjoinRoot.mk g).comp Polynomial.C = AdjoinRoot.of g from rfl,
    ← AdjoinRoot.algebraMap_eq, sup_comm]

end AdjoinRoot

namespace AdjoinRoot

/--
[is_maximal_iff_irreducible_factor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean)
-/
@[path]
lemma is_maximal_iff_irreducible_factor
  [CommRing A] [IsLocalRing A]
  {g : A[X]} [Algebra.IsIntegral A (AdjoinRoot g)]
  {m : Ideal (AdjoinRoot g)} :
-- imply
  m.IsMaximal ↔
    ∃ q : A[X],
    Irreducible
    (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧
    (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣
    (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧
    m = Ideal.map (algebraMap A (AdjoinRoot g))
    (IsLocalRing.maximalIdeal A) ⊔
    Ideal.span {AdjoinRoot.mk g q} := by
-- proof
  constructor
  · intro hm
    have := hm
    exact exists_irreducible_factor_of_is_maximal g m
  · rintro ⟨q, hirr, hdvd, rfl⟩
    exact is_maximal_of_irreducible_factor g q hirr hdvd

end AdjoinRoot

namespace AdjoinRoot

/--
[is_maximal_iff_irreducible_factor_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean)
-/
@[path]
lemma is_maximal_iff_irreducible_factor_of_monic
  [CommRing A] [IsLocalRing A]
  {g : A[X]}
  {m : Ideal (AdjoinRoot g)}
-- given
  (hg : g.Monic) :
-- imply
  m.IsMaximal ↔
    ∃ q : A[X],
    Irreducible
    (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧
    (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣
    (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧
    m = Ideal.map (algebraMap A (AdjoinRoot g))
    (IsLocalRing.maximalIdeal A) ⊔
    Ideal.span {AdjoinRoot.mk g q} := by
-- proof
  have := hg.finite_adjoinRoot
  exact is_maximal_iff_irreducible_factor g m

end AdjoinRoot

/--
[comap_mapRingHom_bot_eq_map_C_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean)
-/
@[path]
private lemma comap_mapRingHom_bot_eq_map_C_ker_eq
  [CommRing A] [IsLocalRing A]
  {I : Ideal A} :
-- imply
  Ideal.comap (Polynomial.mapRingHom (Ideal.Quotient.mk I)) ⊥ =
    Ideal.map Polynomial.C I := by
-- proof
  apply Polynomial.comap_mapRingHom_bot_eq_map_C_ker I

/--
[is_maximal_of_irreducible_factor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean)
-/
@[path]
private lemma is_maximal_of_irreducible_factor_eq
  [CommRing A] [IsLocalRing A]
  {g q : A[X]}
-- given
  (hirr : Irreducible (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))
  (hdvd : (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣ (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
-- imply
  (Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ⊔
    Ideal.span {AdjoinRoot.mk g q}).IsMaximal := by
-- proof
  apply AdjoinRoot.is_maximal_of_irreducible_factor g q hirr hdvd


-- created on 2026-10-20
-- updated on 2026-10-23
