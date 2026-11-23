import Mathlib
import Def.MvPolynomial_CrossingResolutionScheme
import Instance.MvPolynomial_CrossingResolutionFibrePoints
import Abbrev.MvPolynomial_CrossingResolutionFibrePoints

set_option maxHeartbeats 200000
set_option autoImplicit false

noncomputable section

open Polynomial LaurentPolynomial

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W)

variable (ht : t ∈ 𝔭)
include ht

def originHom : CrossingQuotient W t →ₐ[W] W ⧸ 𝔭 :=
  lift t 0 0 (by rw [mul_zero, algebraMap_quotient_eq_zero t 𝔭 ht])

def lineVHom : CrossingQuotient W t →ₐ[W] (W ⧸ 𝔭)[X] :=
  lift t Polynomial.X 0 (by rw [mul_zero, algebraMap_poly_eq_zero t 𝔭 ht])

def lineUHom : CrossingQuotient W t →ₐ[W] (W ⧸ 𝔭)[X] :=
  lift t 0 Polynomial.X (by rw [zero_mul, algebraMap_poly_eq_zero t 𝔭 ht])

def originIdeal : Ideal (CrossingQuotient W t) := RingHom.ker (originHom t 𝔭 ht).toRingHom

def lineVIdeal : Ideal (CrossingQuotient W t) := RingHom.ker (lineVHom t 𝔭 ht).toRingHom

def lineUIdeal : Ideal (CrossingQuotient W t) := RingHom.ker (lineUHom t 𝔭 ht).toRingHom

def lineULaurent : CrossingQuotient W t →+* LaurentPolynomial (W ⧸ 𝔭) :=
  (toLaurent : (W ⧸ 𝔭)[X] →+* LaurentPolynomial (W ⧸ 𝔭)).comp (lineUHom t 𝔭 ht).toRingHom

def overlapHom : Localization.Away (V t) →+* LaurentPolynomial (W ⧸ 𝔭) :=
  IsLocalization.Away.lift (V t) (isUnit_lineULaurent_V t 𝔭 ht)

def overlapIdeal : Ideal (Localization.Away (V t)) := RingHom.ker (overlapHom t 𝔭 ht)

omit ht in
variable (e : ℕ)

def vertexIdeal (he : 1 ≤ e) : Ideal (CrossingQuotient W (t ^ e)) := originIdeal (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e he)

def branchVPrime (he : 1 ≤ e) : Ideal (CrossingQuotient W (t ^ e)) := lineVIdeal (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e he)

def branchUPrime (he : 1 ≤ e) : Ideal (CrossingQuotient W (t ^ e)) := lineUIdeal (t ^ e) 𝔭 (t_pow_mem t 𝔭 ht e he)

omit ht in
end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open Polynomial

universe u

variable {W : Type u} [CommRing W] (t : W)

def quotBase (I : Ideal (CrossingQuotient W t)) (hI : algebraMap W (CrossingQuotient W t) t ∈ I) :
    (W ⧸ Ideal.span ({t} : Set W)) →ₐ[W] CrossingQuotient W t ⧸ I :=
  Ideal.Quotient.liftₐ (Ideal.span {t}) ((Ideal.Quotient.mkₐ W I).comp (Algebra.ofId W _)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    change Ideal.Quotient.mk I (algebraMap W (CrossingQuotient W t) (c * t)) = 0
    rw [map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_left _ hI))

def quotSpanUEquiv_fwd : (CrossingQuotient W t ⧸ Ideal.span {U t}) →ₐ[W] (W ⧸ Ideal.span ({t} : Set W))[X] :=
  Ideal.Quotient.liftₐ (Ideal.span {U t}) (lineUHom t (Ideal.span {t}) (mem_span_t t)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, lineUHom_U, mul_zero])

def quotSpanUEquiv_bwd : (W ⧸ Ideal.span ({t} : Set W))[X] →ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {U t}) :=
  Polynomial.aevalTower (quotBase t _ (algebraMap_mem_span_U t)) (Ideal.Quotient.mk _ (V t))

def quotSpanUEquiv : (CrossingQuotient W t ⧸ Ideal.span {U t}) ≃ₐ[W] (W ⧸ Ideal.span ({t} : Set W))[X] :=
  AlgEquiv.ofAlgHom (quotSpanUEquiv_fwd t) (quotSpanUEquiv_bwd t) (quotSpanUEquiv_fwd_bwd t) (quotSpanUEquiv_bwd_fwd t)

def quotSpanVEquiv_fwd : (CrossingQuotient W t ⧸ Ideal.span {V t}) →ₐ[W] (W ⧸ Ideal.span ({t} : Set W))[X] :=
  Ideal.Quotient.liftₐ (Ideal.span {V t}) (lineVHom t (Ideal.span {t}) (mem_span_t t)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, lineVHom_V, mul_zero])

def quotSpanVEquiv_bwd : (W ⧸ Ideal.span ({t} : Set W))[X] →ₐ[W] (CrossingQuotient W t ⧸ Ideal.span {V t}) :=
  Polynomial.aevalTower (quotBase t _ (algebraMap_mem_span_V t)) (Ideal.Quotient.mk _ (U t))

def quotSpanVEquiv : (CrossingQuotient W t ⧸ Ideal.span {V t}) ≃ₐ[W] (W ⧸ Ideal.span ({t} : Set W))[X] :=
  AlgEquiv.ofAlgHom (quotSpanVEquiv_fwd t) (quotSpanVEquiv_bwd t) (quotSpanVEquiv_fwd_bwd t) (quotSpanVEquiv_bwd_fwd t)

end MvPolynomial.CrossingQuotient

end


noncomputable section

namespace MvPolynomial.CrossingQuotient

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) (ht : t ∈ 𝔭)
include ht

variable (e : ℕ)

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open Polynomial

universe u

variable {W : Type u} [CommRing W] (t : W) (𝔭 : Ideal W) (ht : t ∈ 𝔭)

def quotBaseP (I : Ideal (CrossingQuotient W t)) (hI : 𝔭.map (algebraMap W (CrossingQuotient W t)) ≤ I) :
    (W ⧸ 𝔭) →ₐ[W] CrossingQuotient W t ⧸ I :=
  Ideal.Quotient.liftₐ 𝔭 ((Ideal.Quotient.mkₐ W I).comp (Algebra.ofId W _)) (by
    intro a ha
    change Ideal.Quotient.mk I (algebraMap W (CrossingQuotient W t) a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI (Ideal.mem_map_of_mem _ ha)))

section lineU

def quotIUEquiv_fwd : (CrossingQuotient W t ⧸ IU t 𝔭) →ₐ[W] (W ⧸ 𝔭)[X] :=
  Ideal.Quotient.liftₐ (IU t 𝔭) (lineUHom t 𝔭 ht) (fun a ha =>
    (mem_lineUIdeal_iff t 𝔭 ht a).mp (span_U_sup_map_le_lineUIdeal t 𝔭 ht ha))

def quotIUEquiv_bwd : (W ⧸ 𝔭)[X] →ₐ[W] (CrossingQuotient W t ⧸ IU t 𝔭) :=
  Polynomial.aevalTower (quotBaseP t 𝔭 _ le_sup_right) (Ideal.Quotient.mk _ (V t))

def quotIUEquiv : (CrossingQuotient W t ⧸ IU t 𝔭) ≃ₐ[W] (W ⧸ 𝔭)[X] :=
  AlgEquiv.ofAlgHom (quotIUEquiv_fwd t 𝔭 ht) (quotIUEquiv_bwd t 𝔭) (quotIUEquiv_fwd_bwd t 𝔭 ht)
    (quotIUEquiv_bwd_fwd t 𝔭 ht)

end lineU

section lineV

def quotIVEquiv_fwd : (CrossingQuotient W t ⧸ IV t 𝔭) →ₐ[W] (W ⧸ 𝔭)[X] :=
  Ideal.Quotient.liftₐ (IV t 𝔭) (lineVHom t 𝔭 ht) (fun a ha =>
    (mem_lineVIdeal_iff t 𝔭 ht a).mp (span_V_sup_map_le_lineVIdeal t 𝔭 ht ha))

def quotIVEquiv_bwd : (W ⧸ 𝔭)[X] →ₐ[W] (CrossingQuotient W t ⧸ IV t 𝔭) :=
  Polynomial.aevalTower (quotBaseP t 𝔭 _ le_sup_right) (Ideal.Quotient.mk _ (U t))

def quotIVEquiv : (CrossingQuotient W t ⧸ IV t 𝔭) ≃ₐ[W] (W ⧸ 𝔭)[X] :=
  AlgEquiv.ofAlgHom (quotIVEquiv_fwd t 𝔭 ht) (quotIVEquiv_bwd t 𝔭) (quotIVEquiv_fwd_bwd t 𝔭 ht)
    (quotIVEquiv_bwd_fwd t 𝔭 ht)

end lineV

end MvPolynomial.CrossingQuotient

end

noncomputable section

namespace MvPolynomial.CrossingQuotient

open AlgebraicGeometry CategoryTheory GlueIndex

universe u

variable {W : Type u} [CommRing W] (t : W)

namespace Resolution

variable (e : ℕ)

variable (𝔭 : Ideal W) [𝔭.IsPrime] (ht : t ∈ 𝔭)

def chartPt (i : Fin e) (P : Ideal (CrossingQuotient W t)) [P.IsPrime] : Resolution t e :=
  ι t e i ⟨P, inferInstance⟩

def origin (i : Fin e) : Resolution t e := chartPt t e i (originIdeal t 𝔭 ht)

def lineGen (i : Fin e) : Resolution t e := chartPt t e i (lineVIdeal t 𝔭 ht)

def lineUGen (i : Fin e) : Resolution t e := chartPt t e i (lineUIdeal t 𝔭 ht)

def vertexPt (he : 1 ≤ e) : crossingScheme (t ^ e) := ⟨vertexIdeal t 𝔭 ht e he, inferInstance⟩

def branchVPt (he : 1 ≤ e) : crossingScheme (t ^ e) := ⟨branchVPrime t 𝔭 ht e he, inferInstance⟩

def branchUPt (he : 1 ≤ e) : crossingScheme (t ^ e) := ⟨branchUPrime t 𝔭 ht e he, inferInstance⟩

end Resolution

end MvPolynomial.CrossingQuotient

end
