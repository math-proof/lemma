import Mathlib
import Lemma.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld
namespace EdgeFamily

variable (p : ℕ) [Fact p.Prime]

def wittDigit {R : Type*} [CommRing R] (x : R) (j : ℕ) : R :=
  (WittVector.frobenius (WittVector.teichmuller p x) - WittVector.teichmuller p x).coeff j

def branchConstants {R : Type*} [CommRing R] (x : R) (m : ℕ) : R :=
  if m = 0 then x ^ p - x
  else if m = 1 then 1
  else if m % 2 = 0 then wittDigit p x (m / 2) ^ p ^ (m / 2)
  else 0

def edgeConstants {R : Type*} [CommRing R] (ξ η : R) : ℕ → Fin 2 → R :=
  fun m i => if i = 0 then branchConstants p η m else branchConstants p ξ m

variable {p}

@[simp] theorem branchConstants_zero {R : Type*} [CommRing R] (x : R) : branchConstants p x 0 = x ^ p - x := by
  simp [branchConstants]

@[simp] theorem branchConstants_one {R : Type*} [CommRing R] (x : R) : branchConstants p x 1 = 1 := by
  simp [branchConstants]

@[simp] theorem edgeConstants_zero_zero {R : Type*} [CommRing R] (ξ η : R) : edgeConstants p ξ η 0 0 = η ^ p - η := by
  simp [edgeConstants]

@[simp] theorem edgeConstants_zero_one {R : Type*} [CommRing R] (ξ η : R) : edgeConstants p ξ η 0 1 = ξ ^ p - ξ := by
  simp [edgeConstants]

@[simp] theorem edgeConstants_one {R : Type*} [CommRing R] (ξ η : R) (i : Fin 2) : edgeConstants p ξ η 1 i = 1 := by
  fin_cases i <;> simp [edgeConstants]

theorem edgeConstants_zero_zero_mul_zero_one {R : Type*} [CommRing R] (ξ η : R) (h : ξ * η = 0) :
    edgeConstants p ξ η 0 0 * edgeConstants p ξ η 0 1 = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  simp only [edgeConstants_zero_zero, edgeConstants_zero_one]
  have : (η ^ p - η) * (ξ ^ p - ξ) = (ξ * η) * ((η ^ n - 1) * (ξ ^ n - 1)) := by
    rw [hn]; ring
  rw [this, h, zero_mul]

theorem edgeConstants_zero_zero_mul_zero_one_eq_natCast {R : Type*} [CommRing R] (ξ η : R) (h : ξ * η = 0)
    (hp0 : (p : R) = 0) : edgeConstants p ξ η 0 0 * edgeConstants p ξ η 0 1 = (p : R) := by
  rw [edgeConstants_zero_zero_mul_zero_one ξ η h, hp0]

theorem wittDigit_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (j : ℕ) :
    f (wittDigit p x j) = wittDigit p (f x) j := by
  have h1 : WittVector.map f (WittVector.frobenius (WittVector.teichmuller p x)) =
      WittVector.frobenius (WittVector.map f (WittVector.teichmuller p x)) := by
    exact (WittVector.frobenius_isPoly p).map f _
  simp only [wittDigit]
  rw [← WittVector.map_coeff, map_sub, h1, WittVector.map_teichmuller]

theorem branchConstants_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (x : R) (m : ℕ) :
    f (branchConstants p x m) = branchConstants p (f x) m := by
  simp only [branchConstants]
  split_ifs <;> simp [map_sub, map_pow, wittDigit_map]

theorem edgeConstants_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (ξ η : R) (m : ℕ) (i : Fin 2) :
    f (edgeConstants p ξ η m i) = edgeConstants p (f ξ) (f η) m i := by
  simp only [edgeConstants]
  split_ifs <;> exact branchConstants_map f _ m

variable (p)

abbrev edgeRingCharP (k : Type) [CommRing k] : Type := FormalOmega.chartERing k (0 : k) p

abbrev edgeRingCharP.ξ (k : Type) [CommRing k] : edgeRingCharP p k := FormalOmega.chartERing.ξ k (0 : k) p

abbrev edgeRingCharP.η (k : Type) [CommRing k] : edgeRingCharP p k := FormalOmega.chartERing.η k (0 : k) p

omit [Fact p.Prime] in
theorem edgeRingCharP.ξ_mul_η (k : Type) [CommRing k] : edgeRingCharP.ξ p k * edgeRingCharP.η p k = 0 := by
  rw [edgeRingCharP.ξ, edgeRingCharP.η, FormalOmega.chartERing.ξ_mul_η, map_zero]

abbrev edgeRingConstants (k : Type) [CommRing k] : ℕ → Fin 2 → edgeRingCharP p k :=
  edgeConstants p (edgeRingCharP.ξ p k) (edgeRingCharP.η p k)

theorem edgeRingConstants_mul (k : Type) [CommRing k] [CharP k p] :
    edgeRingConstants p k 0 0 * edgeRingConstants p k 0 1 = (p : edgeRingCharP p k) := by
  apply edgeConstants_zero_zero_mul_zero_one_eq_natCast _ _ (edgeRingCharP.ξ_mul_η p k)
  rw [← map_natCast (algebraMap k (edgeRingCharP p k)), CharP.cast_eq_zero, map_zero]

end EdgeFamily
end CerednikDrinfeld

end
