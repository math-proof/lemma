import Mathlib
import Lemma.WeierstrassCurve.VeluQuotientOfSums
import Def.WeierstrassCurve_KohelQuotient

set_option autoImplicit false

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]


@[simp] theorem rootESymm_zero_right (h : R[X]) : h.rootESymm 0 = h.leadingCoeff := by
  simp only [rootESymm, zero_le, if_true, pow_zero, one_mul, Nat.sub_zero]
  rfl

theorem rootESymm_of_lt {h : R[X]} {k : ℕ} (hk : h.natDegree < k) : h.rootESymm k = 0 := by
  simp [rootESymm, not_le.mpr hk]

theorem rootESymm_of_le {h : R[X]} {k : ℕ} (hk : k ≤ h.natDegree) :
    h.rootESymm k = (-1) ^ k * h.coeff (h.natDegree - k) := by
  simp [rootESymm, hk]

@[simp] theorem rootESymm_one (k : ℕ) : (1 : R[X]).rootESymm k = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · simp
  · simp [rootESymm]

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem rootESymm_map {h : R[X]} (hh : f h.leadingCoeff ≠ 0) (k : ℕ) :
    (h.map f).rootESymm k = f (h.rootESymm k) := by
  simp only [rootESymm, natDegree_map_of_leadingCoeff_ne_zero f hh, coeff_map]
  split_ifs <;> simp

theorem rootESymm_map_of_monic {h : R[X]} (hh : h.Monic) (k : ℕ) :
    (h.map f).rootESymm k = f (h.rootESymm k) := by
  nontriviality S
  exact rootESymm_map f (by rw [hh.leadingCoeff, map_one]; exact one_ne_zero) k

theorem rootPowerSumOne_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumOne = f h.rootPowerSumOne := by
  simp [rootPowerSumOne, rootESymm_map_of_monic f hh]

theorem rootPowerSumTwo_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumTwo = f h.rootPowerSumTwo := by
  simp [rootPowerSumTwo, rootESymm_map_of_monic f hh, map_ofNat]

theorem rootPowerSumThree_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumThree = f h.rootPowerSumThree := by
  simp [rootPowerSumThree, rootESymm_map_of_monic f hh, map_ofNat]

end map

end Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


@[simp] theorem kohelQuotient_a₁ (h : R[X]) : (W.kohelQuotient h).a₁ = W.a₁ := rfl
@[simp] theorem kohelQuotient_a₂ (h : R[X]) : (W.kohelQuotient h).a₂ = W.a₂ := rfl
@[simp] theorem kohelQuotient_a₃ (h : R[X]) : (W.kohelQuotient h).a₃ = W.a₃ := rfl
theorem kohelQuotient_a₄ (h : R[X]) : (W.kohelQuotient h).a₄ = W.a₄ - 5 * W.kohelT h := rfl
theorem kohelQuotient_a₆ (h : R[X]) :
    (W.kohelQuotient h).a₆ = W.a₆ - W.b₂ * W.kohelT h - 7 * W.kohelW h := rfl

theorem kohelQuotient_b₂ (h : R[X]) : (W.kohelQuotient h).b₂ = W.b₂ := by
  simp [b₂]

@[simp] theorem kohelT_one : W.kohelT 1 = 0 := by
  simp [kohelT, rootPowerSumOne, rootPowerSumTwo]

@[simp] theorem kohelW_one : W.kohelW 1 = 0 := by
  simp [kohelW, rootPowerSumOne, rootPowerSumTwo, rootPowerSumThree]

@[simp] theorem kohelQuotient_one : W.kohelQuotient 1 = W := by
  ext <;> simp [kohelQuotient, veluQuotientOfSums]

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem map_kohelT {h : R[X]} (hh : h.Monic) : f (W.kohelT h) = (W.map f).kohelT (h.map f) := by
  nontriviality S
  simp [kohelT, rootPowerSumOne_map_of_monic f hh, rootPowerSumTwo_map_of_monic f hh,
    hh.natDegree_map, map_ofNat]

theorem map_kohelW {h : R[X]} (hh : h.Monic) : f (W.kohelW h) = (W.map f).kohelW (h.map f) := by
  nontriviality S
  simp [kohelW, rootPowerSumOne_map_of_monic f hh, rootPowerSumTwo_map_of_monic f hh,
    rootPowerSumThree_map_of_monic f hh, hh.natDegree_map, map_ofNat]

theorem map_kohelQuotient {h : R[X]} (hh : h.Monic) :
    (W.kohelQuotient h).map f = (W.map f).kohelQuotient (h.map f) := by
  ext
  · rfl
  · rfl
  · rfl
  · simp [kohelQuotient, veluQuotientOfSums, map_kohelT W f hh, map_ofNat]
  · simp [kohelQuotient, veluQuotientOfSums, map_kohelT W f hh, map_kohelW W f hh, map_ofNat]

theorem kohelQuotient_map_j {K L : Type*} [Field K] [Field L] (f : K →+* L) (V : WeierstrassCurve K)
    {h : K[X]} (hh : h.Monic) [(V.kohelQuotient h).IsElliptic]
    [((V.map f).kohelQuotient (h.map f)).IsElliptic] :
    ((V.map f).kohelQuotient (h.map f)).j = f (V.kohelQuotient h).j := by
  have := (V.kohelQuotient h).map_j f
  simp only [map_kohelQuotient V f hh] at this
  convert this using 2

end map

end WeierstrassCurve
