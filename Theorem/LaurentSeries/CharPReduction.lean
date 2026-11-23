module

public import Theorem.LaurentSeries.LaurentCoeff
public import Theorem.HahnSeries.JqCoeff

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace CharPReduction

section IntegralCoeffs

variable {L : Type*} [CommRing L] (A : Subring L)


public theorem mem_integralCoeffs {x : LaurentSeries L} :
    x ∈ integralCoeffs A ↔ ∀ n : ℤ, x.coeff n ∈ A :=
  Iff.rfl


public theorem coeffMap_subtype_packCoeffs (x : integralCoeffs A) :
    coeffMap A.subtype (packCoeffs A x) = (x : LaurentSeries L) := by
  ext n
  rfl


public theorem coeffMap_subtype_injective :
    Function.Injective (coeffMap A.subtype : LaurentSeries A →+* LaurentSeries L) := by
  intro x y h
  ext n
  exact congrArg (fun z : LaurentSeries L => z.coeff n) h


@[simp]
public theorem coeffRed_coeff (x : integralCoeffs A) (n : ℤ) :
    (coeffRed A red x).coeff n = red ⟨(x : LaurentSeries L).coeff n, x.2 n⟩ :=
  rfl

end IntegralCoeffs

section Reduction

variable {L : Type*} [CommRing L] {k : Type*} [Field k]
variable (A : Subring L) (red : A →+* k)
variable (R : Subring (LaurentSeries L)) (hR : R ≤ integralCoeffs A)


public theorem redRes_apply (r : R) :
    redRes A red R hR r = coeffRed A red ⟨(r : LaurentSeries L), hR r.2⟩ :=
  rfl


public theorem redKer_isPrime : (redKer A red R hR).IsPrime :=
  RingHom.ker_isPrime _


public theorem notMem_redKer_iff {s : R} :
    s ∉ redKer A red R hR ↔ redRes A red R hR s ≠ 0 := by
  rw [redKer, not_iff_not, RingHom.mem_ker]


public theorem one_notMem_redKer : (1 : R) ∉ redKer A red R hR := by
  rw [notMem_redKer_iff, map_one]
  exact one_ne_zero


public theorem mem_localizedAtKer {f : LaurentSeries L} :
    f ∈ localizedAtKer A red R hR ↔
      ∃ r s : R, s ∉ redKer A red R hR ∧ f * s = r :=
  Iff.rfl


public theorem subring_le_localizedAtKer : R ≤ localizedAtKer A red R hR := fun r hr =>
  ⟨⟨r, hr⟩, 1, one_notMem_redKer A red R hR, by simp⟩

end Reduction

section LocalizedReduction

variable {L : Type*} [CommRing L] {k : Type*} [Field k]
variable {A : Subring L} {red : A →+* k}
variable {R : Subring (LaurentSeries L)} {hR : R ≤ integralCoeffs A}

open Classical in


public theorem redRes_ne_zero_of_notMem {s : R} (hs : s ∉ redKer A red R hR) :
    redRes A red R hR s ≠ 0 :=
  (notMem_redKer_iff A red R hR).mp hs


public theorem redLoc_spec (f : localizedAtKer A red R hR) {r s : R}
    (hfs : (f : LaurentSeries L) * s = r) :
    redLoc f * redRes A red R hR s = redRes A red R hR r := by
  obtain ⟨hs₀, hfs₀⟩ := Classical.choose_spec (Classical.choose_spec f.2)
  have hs₀ne : redRes A red R hR (Classical.choose (Classical.choose_spec f.2)) ≠ 0 :=
    redRes_ne_zero_of_notMem (A := A) (red := red) (R := R) (hR := hR) hs₀
  have hcross : Classical.choose f.2 * s
      = r * Classical.choose (Classical.choose_spec f.2) := by
    have h : ((Classical.choose f.2 : R) : LaurentSeries L) * (s : LaurentSeries L)
        = (r : LaurentSeries L)
          * ((Classical.choose (Classical.choose_spec f.2) : R) : LaurentSeries L) := by
      linear_combination
        ((Classical.choose (Classical.choose_spec f.2) : R) : LaurentSeries L) * hfs
          - (s : LaurentSeries L) * hfs₀
    exact_mod_cast h
  have hred := congrArg (redRes A red R hR) hcross
  rw [map_mul, map_mul] at hred
  apply mul_right_cancel₀ hs₀ne
  calc redLoc f * redRes A red R hR s
        * redRes A red R hR (Classical.choose (Classical.choose_spec f.2))
      = redRes A red R hR (Classical.choose f.2) * redRes A red R hR s
        * ((redRes A red R hR (Classical.choose (Classical.choose_spec f.2)))⁻¹
          * redRes A red R hR (Classical.choose (Classical.choose_spec f.2))) := by
        rw [redLoc]; ring
    _ = redRes A red R hR (Classical.choose f.2) * redRes A red R hR s := by
        rw [inv_mul_cancel₀ hs₀ne, mul_one]
    _ = redRes A red R hR r
        * redRes A red R hR (Classical.choose (Classical.choose_spec f.2)) := hred


public theorem redLoc_coe (r : R) :
    redLoc ⟨(r : LaurentSeries L), subring_le_localizedAtKer A red R hR r.2⟩
      = redRes A red R hR r := by
  have h := redLoc_spec (A := A) (red := red) (R := R) (hR := hR)
    ⟨(r : LaurentSeries L), subring_le_localizedAtKer A red R hR r.2⟩
    (r := r) (s := 1) (by simp)
  rwa [map_one, mul_one] at h


@[simp]
public theorem redLocHom_apply (f : localizedAtKer A red R hR) : redLocHom f = redLoc f :=
  rfl

end LocalizedReduction

section Modular

variable (N : ℕ) [NeZero N]
variable {L : Type*} [CommRing L] (A : Subring L)


public theorem jqModC_mem_modularRing : jqModC L ∈ modularRing N A :=
  Subring.subset_closure (Or.inr (Set.mem_insert _ _))


public theorem jqNModC_mem_modularRing : jqNModC L N ∈ modularRing N A :=
  Subring.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))


public theorem constSeries_mem_modularRing (a : A) : constSeries A a ∈ modularRing N A :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)


public theorem jqModC_mem_integralCoeffs : jqModC L ∈ integralCoeffs A := by
  intro n
  rw [jqModC_eq_map_intCast, HahnSeries.map_coeff]
  exact intCast_mem A _


public theorem jqNModC_mem_integralCoeffs : jqNModC L N ∈ integralCoeffs A := by
  intro n
  by_cases h : ((N : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [jqNModC, qExpand_coeff_mul]
    exact jqModC_mem_integralCoeffs A m
  · rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h]
    exact A.zero_mem


public theorem constSeries_mem_integralCoeffs (a : A) :
    constSeries A a ∈ integralCoeffs A := by
  intro n
  have : constSeries A a = HahnSeries.single 0 (a : L) := by
    show algebraMap L (LaurentSeries L) (a : L) = HahnSeries.single 0 (a : L)
    ext m
    rw [HahnSeries.algebraMap_apply', show algebraMap L (PowerSeries L) (a : L)
      = PowerSeries.C (a : L) from by simp, HahnSeries.ofPowerSeries_C]
    rfl
  rw [this, HahnSeries.coeff_single]
  split_ifs
  · exact a.2
  · exact A.zero_mem


public theorem modularRing_le_integralCoeffs : modularRing N A ≤ integralCoeffs A := by
  rw [modularRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact constSeries_mem_integralCoeffs A a
  · exact jqModC_mem_integralCoeffs A
  · exact jqNModC_mem_integralCoeffs N A

variable {k : Type*} [Field k] (red : A →+* k)

