import Mathlib
import Def.Algebra.AdicCompletion.PolynomialCompletion.Part3
set_option autoImplicit false


namespace Localization.AtPrime

variable {R : Type*} [CommRing R] (q : Ideal R) [hq : q.IsMaximal]

open IsLocalRing

theorem quotientPowMap_mk (n : ℕ) (x : R) :
    quotientPowMap q n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R _ x) :=
  Ideal.quotientMap_mk

theorem exists_mul_add_eq_one_of_notMem (n : ℕ) {s : R} (hs : s ∉ q) :
    ∃ a, ∃ c ∈ q ^ n, a * s + c = 1 := by
  have htop : q ⊔ Ideal.span {s} = ⊤ := by
    obtain ⟨y, i, hi, h⟩ := hq.exists_inv hs
    rw [Ideal.eq_top_iff_one, ← h, sup_comm]
    exact Submodule.add_mem_sup (Ideal.mem_span_singleton'.mpr ⟨y, rfl⟩) hi
  have h1 : (1 : R) ∈ q ^ n ⊔ Ideal.span {s} := by
    rw [Ideal.pow_sup_eq_top htop]; trivial
  obtain ⟨c, hc, z, hz, hcz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  exact ⟨a, c, hc, by rw [add_comm, hcz]⟩

theorem quotientPowMap_bijective (n : ℕ) : Function.Bijective (quotientPowMap q n) := by
  constructor
  · exact Ideal.quotientMap_injective' (comap_maximalIdeal_pow q n).le
  · intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨a, c, hc, hac⟩ := exists_mul_add_eq_one_of_notMem q n (s := (s : R)) s.prop
    refine ⟨Ideal.Quotient.mk _ (r * a), ?_⟩
    rw [quotientPowMap_mk, Ideal.Quotient.eq]
    have hs : (algebraMap R (Localization.AtPrime q)) (s : R) * IsLocalization.mk' _ r s
        = algebraMap R _ r := IsLocalization.mk'_spec' _ r s
    have : algebraMap R (Localization.AtPrime q) (r * a) - IsLocalization.mk' _ r s
        = - (IsLocalization.mk' (Localization.AtPrime q) r s * algebraMap R _ c) := by
      have hc' : algebraMap R (Localization.AtPrime q) (a * s) = 1 - algebraMap R _ c := by
        rw [eq_sub_iff_add_eq, ← map_add, hac, map_one]
      rw [map_mul, ← hs, mul_comm (algebraMap R _ (s : R)), mul_assoc, ← map_mul,
        mul_comm (s : R), hc']
      ring
    rw [this]
    refine neg_mem (Ideal.mul_mem_left _ _ ?_)
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hc

end Localization.AtPrime
