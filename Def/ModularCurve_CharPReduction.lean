module

public import Theorem.LaurentSeries.LaurentCoeff
public import Theorem.HahnSeries.JqCoeff

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace CharPReduction

section IntegralCoeffs

variable {L : Type*} [CommRing L] (A : Subring L)

def integralCoeffs : Subring (LaurentSeries L) where
  carrier := {x | ∀ n : ℤ, x.coeff n ∈ A}
  zero_mem' := fun n => by simp
  one_mem' := fun n => by
    rw [HahnSeries.coeff_one]
    split_ifs
    · exact A.one_mem
    · exact A.zero_mem
  add_mem' := fun hx hy n => by
    rw [HahnSeries.coeff_add]
    exact A.add_mem (hx n) (hy n)
  neg_mem' := fun hx n => by
    rw [HahnSeries.coeff_neg]
    exact A.neg_mem (hx n)
  mul_mem' := fun hx hy n => by
    rw [HahnSeries.coeff_mul]
    exact A.sum_mem fun ij _ => A.mul_mem (hx ij.1) (hy ij.2)

private def packCoeffs (x : integralCoeffs A) : LaurentSeries A where
  coeff n := ⟨(x : LaurentSeries L).coeff n, x.2 n⟩
  isPWO_support' := (x : LaurentSeries L).isPWO_support.mono
    (fun _ hn h => hn (Subtype.ext h))

private def packCoeffsHom : integralCoeffs A →+* LaurentSeries A where
  toFun := packCoeffs A
  map_one' := coeffMap_subtype_injective A <| by
    rw [coeffMap_subtype_packCoeffs, map_one, OneMemClass.coe_one]
  map_mul' x y := coeffMap_subtype_injective A <| by
    rw [map_mul, coeffMap_subtype_packCoeffs, coeffMap_subtype_packCoeffs,
      coeffMap_subtype_packCoeffs, MulMemClass.coe_mul]
  map_zero' := coeffMap_subtype_injective A <| by
    rw [coeffMap_subtype_packCoeffs, map_zero, ZeroMemClass.coe_zero]
  map_add' x y := coeffMap_subtype_injective A <| by
    rw [map_add, coeffMap_subtype_packCoeffs, coeffMap_subtype_packCoeffs,
      coeffMap_subtype_packCoeffs, AddMemClass.coe_add]

variable {k : Type*} [CommRing k] (red : A →+* k)

def coeffRed : integralCoeffs A →+* LaurentSeries k :=
  (coeffMap red).comp (packCoeffsHom A)

end IntegralCoeffs

section Reduction

variable {L : Type*} [CommRing L] {k : Type*} [Field k]
variable (A : Subring L) (red : A →+* k)
variable (R : Subring (LaurentSeries L)) (hR : R ≤ integralCoeffs A)

def redRes : R →+* LaurentSeries k :=
  (coeffRed A red).comp (Subring.inclusion hR)

def redKer : Ideal R :=
  RingHom.ker (redRes A red R hR)

def localizedAtKer : Subring (LaurentSeries L) where
  carrier := {f | ∃ r s : R, s ∉ redKer A red R hR ∧ f * s = r}
  zero_mem' := ⟨0, 1, one_notMem_redKer A red R hR, by simp⟩
  one_mem' := ⟨1, 1, one_notMem_redKer A red R hR, by simp⟩
  add_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * t + u * s, s * t, fun hmem =>
      (((redKer_isPrime A red R hR).mem_or_mem hmem).elim hs ht), ?_⟩
    push_cast
    calc (f + g) * ((s : LaurentSeries L) * t)
        = f * s * t + g * t * s := by ring
      _ = (r : LaurentSeries L) * t + u * s := by rw [hf, hg]
  neg_mem' := by
    rintro f ⟨r, s, hs, hf⟩
    exact ⟨-r, s, hs, by push_cast; rw [neg_mul, hf]⟩
  mul_mem' := by
    rintro f g ⟨r, s, hs, hf⟩ ⟨u, t, ht, hg⟩
    refine ⟨r * u, s * t, fun hmem =>
      (((redKer_isPrime A red R hR).mem_or_mem hmem).elim hs ht), ?_⟩
    push_cast
    calc f * g * ((s : LaurentSeries L) * t)
        = (f * s) * (g * t) := by ring
      _ = (r : LaurentSeries L) * u := by rw [hf, hg]

end Reduction

section LocalizedReduction

variable {L : Type*} [CommRing L] {k : Type*} [Field k]
variable {A : Subring L} {red : A →+* k}
variable {R : Subring (LaurentSeries L)} {hR : R ≤ integralCoeffs A}

open Classical in

def redLoc (f : localizedAtKer A red R hR) : LaurentSeries k :=
  redRes A red R hR (Classical.choose f.2) *
    (redRes A red R hR (Classical.choose (Classical.choose_spec f.2)))⁻¹

def redLocHom : localizedAtKer A red R hR →+* LaurentSeries k where
  toFun := redLoc
  map_one' := by
    have h := redLoc_spec (A := A) (red := red) (R := R) (hR := hR)
      (1 : localizedAtKer A red R hR) (r := 1) (s := 1) (by simp)
    rwa [map_one, mul_one] at h
  map_mul' f g := by
    obtain ⟨r, s, hs, hf⟩ := f.2
    obtain ⟨u, t, ht, hg⟩ := g.2
    have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := R) (hR := hR) hs
    have htne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := R) (hR := hR) ht
    have hfg : ((f * g : localizedAtKer A red R hR) : LaurentSeries L)
        * ((s * t : R) : LaurentSeries L) = ((r * u : R) : LaurentSeries L) := by
      push_cast
      calc (f : LaurentSeries L) * g * ((s : LaurentSeries L) * t)
          = ((f : LaurentSeries L) * s) * ((g : LaurentSeries L) * t) := by ring
        _ = (r : LaurentSeries L) * u := by rw [hf, hg]
    have h2 := redLoc_spec (f * g) hfg
    have hfspec := redLoc_spec f hf
    have hgspec := redLoc_spec g hg
    apply mul_right_cancel₀ (mul_ne_zero hsne htne)
    calc redLoc (f * g) * (redRes A red R hR s * redRes A red R hR t)
        = redLoc (f * g) * redRes A red R hR (s * t) := by rw [map_mul]
      _ = redRes A red R hR (r * u) := h2
      _ = (redLoc f * redRes A red R hR s) * (redLoc g * redRes A red R hR t) := by
          rw [map_mul, hfspec, hgspec]
      _ = redLoc f * redLoc g * (redRes A red R hR s * redRes A red R hR t) := by ring
  map_zero' := by
    have h := redLoc_spec (A := A) (red := red) (R := R) (hR := hR)
      (0 : localizedAtKer A red R hR) (r := 0) (s := 1) (by simp)
    rwa [map_one, mul_one, map_zero] at h
  map_add' f g := by
    obtain ⟨r, s, hs, hf⟩ := f.2
    obtain ⟨u, t, ht, hg⟩ := g.2
    have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := R) (hR := hR) hs
    have htne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := R) (hR := hR) ht
    have hfg : ((f + g : localizedAtKer A red R hR) : LaurentSeries L)
        * ((s * t : R) : LaurentSeries L) = ((r * t + u * s : R) : LaurentSeries L) := by
      push_cast
      calc ((f : LaurentSeries L) + g) * ((s : LaurentSeries L) * t)
          = ((f : LaurentSeries L) * s) * t + ((g : LaurentSeries L) * t) * s := by ring
        _ = (r : LaurentSeries L) * t + (u : LaurentSeries L) * s := by rw [hf, hg]
    have h2 := redLoc_spec (f + g) hfg
    have hfspec := redLoc_spec f hf
    have hgspec := redLoc_spec g hg
    apply mul_right_cancel₀ (mul_ne_zero hsne htne)
    calc redLoc (f + g) * (redRes A red R hR s * redRes A red R hR t)
        = redLoc (f + g) * redRes A red R hR (s * t) := by rw [map_mul]
      _ = redRes A red R hR (r * t + u * s) := h2
      _ = (redLoc f * redRes A red R hR s) * redRes A red R hR t
          + (redLoc g * redRes A red R hR t) * redRes A red R hR s := by
          rw [map_add, map_mul, map_mul, hfspec, hgspec]
      _ = (redLoc f + redLoc g) * (redRes A red R hR s * redRes A red R hR t) := by ring

end LocalizedReduction

section Modular

variable (N : ℕ) [NeZero N]
variable {L : Type*} [CommRing L] (A : Subring L)

def constSeries : A →+* LaurentSeries L :=
  (algebraMap L (LaurentSeries L)).comp A.subtype

def modularRing : Subring (LaurentSeries L) :=
  Subring.closure (Set.range (constSeries A) ∪ {jqModC L, jqNModC L N})

variable {k : Type*} [Field k] (red : A →+* k)

def modularLocalized : Subring (LaurentSeries L) :=
  localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)

def modularRedLocHom : modularLocalized N A red →+* LaurentSeries k :=
  redLocHom (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A)

end Modular

end CharPReduction
end ModularCurve

end

end
