import Mathlib
import sympy.Basic

open Polynomial

/--
[Polynomial_isReduced_quotient_span_singleton_of_separable_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_isReduced_quotient_span_singleton_of_separable_map.lean)
-/

private lemma  Polynomial.isReduced_quotient_span_singleton_of_separable_map
    {D : Type*} [CommRing D] [IsDomain D] {g : D[X]} (hg : g.Monic)
    (hsep : (g.map (algebraMap D (FractionRing D))).Separable) :
    IsReduced (D[X] ⧸ Ideal.span {g}) := by
  set K := FractionRing D

  let φ : D[X] ⧸ Ideal.span {g} →+* K[X] ⧸ Ideal.span {g.map (algebraMap D K)} :=
    Ideal.Quotient.lift (Ideal.span {g}) ((Ideal.Quotient.mk _).comp (mapRingHom (algebraMap D K)))
      (fun a ha => by
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, coe_mapRingHom, Polynomial.map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, coe_mapRingHom,
      Polynomial.map_dvd_map (algebraMap D K) (IsFractionRing.injective D K) hg] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hx
  have : IsReduced (K[X] ⧸ Ideal.span {g.map (algebraMap D K)}) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp
      (isRadical_iff_span_singleton.mp hsep.squarefree.isRadical)
  exact isReduced_of_injective φ hφ
@[path]
private lemma main
  [CommRing D] [IsDomain D]
  {g : D[X]}
-- given
  (hg : g.Monic)
  (hsep : (g.map (algebraMap D (FractionRing D))).Separable) :
-- imply
  IsReduced (D[X] ⧸ Ideal.span {g}) :=
-- proof
  Polynomial.isReduced_quotient_span_singleton_of_separable_map hg hsep


-- created on 2026-10-05
