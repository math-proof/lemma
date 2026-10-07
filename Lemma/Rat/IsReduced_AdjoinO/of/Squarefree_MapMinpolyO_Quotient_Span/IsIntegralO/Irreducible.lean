import Mathlib
import sympy.Basic

open Polynomial IsLocalRing

/--
[IsDiscreteValuationRing_isReduced_adjoin_singleton_quotient_of_squarefree](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_isReduced_adjoin_singleton_quotient_of_squarefree.lean)
-/
@[main]
private lemma main
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [FaithfulSMul O F]
  {ϖ : O}
  {α : F}
-- given
  (hϖ : Irreducible ϖ)
  (hα : IsIntegral O α)
  (hsq : Squarefree ((minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ})))) :
-- imply
  IsReduced (Algebra.adjoin O {α} ⧸
      Ideal.span {algebraMap O (Algebra.adjoin O {α}) ϖ}) := by
-- proof
  set B : Subalgebra O F := Algebra.adjoin O {α}
  set ϖB : B := algebraMap O B ϖ
  have hmax : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]; infer_instance
  let : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
  have e : AdjoinRoot (minpoly O α) ≃ₐ[O] B := minpoly.equivAdjoin hα
  have hJ : Ideal.span {ϖB} =
      Ideal.map (e : AdjoinRoot (minpoly O α) →+* B)
        (Ideal.map (AdjoinRoot.of (minpoly O α)) (Ideal.span {ϖ})) := by
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
    congr 2
    change algebraMap O B ϖ = e (algebraMap O (AdjoinRoot (minpoly O α)) ϖ)
    rw [AlgEquiv.commutes]
  let e1 := Ideal.quotientEquivAlg
    (Ideal.map (AdjoinRoot.of (minpoly O α)) (Ideal.span {ϖ})) (Ideal.span {ϖB}) e hJ
  let e2 := AdjoinRoot.quotEquivQuotMap (minpoly O α) (Ideal.span {ϖ})
  have : IsReduced ((O ⧸ Ideal.span {ϖ})[X] ⧸
      Ideal.span {(minpoly O α).map (Ideal.Quotient.mk (Ideal.span {ϖ}))}) := by
    rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
    exact hsq.isRadical
  exact isReduced_of_injective (e1.symm.trans e2).toRingEquiv (e1.symm.trans e2).toRingEquiv.injective


-- created on 2026-10-05
