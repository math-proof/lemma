-- Carved from Lemma/Definitions/Def_JacJ1_ChartAlgebra.lean: instance decls only.
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.Perfect
import Class.AlgebraicCurve_DivisorClassGroup

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain IntermediateField

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

scoped instance isPrincipalIdealRing_adjoin_singleton (s : L) :
    IsPrincipalIdealRing (Algebra.adjoin K ({s} : Set L)) :=
  IsPrincipalIdealRing.of_surjective (aevalAdjoin K s).toRingHom (aevalAdjoin_surjective K s)

scoped instance isDedekindDomain_adjoin_singleton (s : L) :
    IsDedekindDomain (Algebra.adjoin K ({s} : Set L)) :=
  inferInstance

instance algebraAdjoin (S : Set L) : Algebra (Algebra.adjoin K S) (chartRing K S) :=
  (Subalgebra.inclusion (adjoin_le_chartRing K S)).toRingHom.toAlgebra

instance isScalarTower_adjoin (S : Set L) :
    IsScalarTower (Algebra.adjoin K S) (chartRing K S) L :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance isScalarTower_base_adjoin (S : Set L) :
    IsScalarTower K (Algebra.adjoin K S) (chartRing K S) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance isIntegralClosure (S : Set L) : IsIntegralClosure (chartRing K S) (Algebra.adjoin K S) L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

section OneGenerator

variable (s : L) [FiniteDimensional K⟮s⟯ L] [CharZero K]

scoped instance charZero_adjoin_simple : CharZero K⟮s⟯ :=
  charZero_of_injective_algebraMap (algebraMap K K⟮s⟯).injective

scoped instance isSeparable_adjoin_simple : Algebra.IsSeparable K⟮s⟯ L :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

open scoped IntermediateField.algebraAdjoinAdjoin in
instance isDedekindDomain_chartRing : IsDedekindDomain (chartRing K ({s} : Set L)) :=
  IsIntegralClosure.isDedekindDomain (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in
instance finite_chartRing :
    Module.Finite (Algebra.adjoin K ({s} : Set L)) (chartRing K ({s} : Set L)) :=
  IsIntegralClosure.finite (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in
instance isFractionRing_chartRing : IsFractionRing (chartRing K ({s} : Set L)) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

instance finiteType_chartRing : Algebra.FiniteType K (chartRing K ({s} : Set L)) :=
  (Algebra.FiniteType.adjoin_of_finite (R := K) (Set.finite_singleton s)).trans
    (inferInstance : Algebra.FiniteType (Algebra.adjoin K ({s} : Set L)) (chartRing K ({s} : Set L)))

instance isNoetherianRing_chartRing : IsNoetherianRing (chartRing K ({s} : Set L)) :=
  inferInstance

end OneGenerator

section Valuation

variable {K}


instance centre_isPrime (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) : (centre K s O hK hs).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, mem_centre_iff]
    simp
  mem_or_mem' {a b} hab := by
    by_contra h
    push Not at h
    rw [mem_centre_iff, Subalgebra.coe_mul, map_mul,
      valuation_eq_one_of_not_mem_centre K s O hK hs h.1,
      valuation_eq_one_of_not_mem_centre K s O hK hs h.2, mul_one] at hab
    exact lt_irrefl _ hab


end Valuation


end CurveModel

end AlgebraicCurve

end
