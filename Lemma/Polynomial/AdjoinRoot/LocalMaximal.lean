import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.AdjoinRoot.LocalMaximal
open Polynomial
open AdjoinRoot


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
[exists_irreducible_factor_of_is_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean)
-/
@[path]
private lemma exists_irreducible_factor_of_is_maximal_eq
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
  apply AdjoinRoot.exists_irreducible_factor_of_is_maximal g m

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

/--
[is_maximal_iff_irreducible_factor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean)
-/
@[path]
private lemma is_maximal_iff_irreducible_factor_eq
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
  apply AdjoinRoot.is_maximal_iff_irreducible_factor g m

/--
[is_maximal_iff_irreducible_factor_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/AdjoinRoot/LocalMaximal.lean)
-/
@[path]
private lemma is_maximal_iff_irreducible_factor_of_monic_eq
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
  apply AdjoinRoot.is_maximal_iff_irreducible_factor_of_monic g hg m


-- created on 2026-10-20
