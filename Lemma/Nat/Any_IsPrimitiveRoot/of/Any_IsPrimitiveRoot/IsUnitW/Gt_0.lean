import Mathlib
import sympy.Basic


/--
[IsAdicComplete_exists_isPrimitiveRoot_of_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAdicComplete_exists_isPrimitiveRoot_of_residueField.lean)
-/
@[main]
private lemma main
  [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
  {n : ℕ}
-- given
  (hn : 0 < n)
  (hnW : IsUnit (n : W))
  (hk : ∃ ζ₀ : IsLocalRing.ResidueField W, IsPrimitiveRoot ζ₀ n) :
-- imply
  ∃ ζ : W, IsPrimitiveRoot ζ n := by
-- proof
  classical
  obtain ⟨ζ₀, hζ₀⟩ := hk
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective ζ₀
  set f : Polynomial W := Polynomial.X ^ n - Polynomial.C 1 with hf
  have hmonic : f.Monic := Polynomial.monic_X_pow_sub_C (1 : W) hn.ne'
  have heval : ∀ a : W, f.eval a = a ^ n - 1 := fun a => by
    simp [hf]
  have hderiv_eval : f.derivative.eval a₀ = (n : W) * a₀ ^ (n - 1) := by
    simp [hf, Polynomial.derivative_X_pow]

  have hroot : f.eval a₀ ∈ IsLocalRing.maximalIdeal W := by
    rw [← IsLocalRing.residue_eq_zero_iff, heval, map_sub, map_pow, ha₀, hζ₀.pow_eq_one, map_one, sub_self]

  have hunit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal W) (f.derivative.eval a₀)) := by
    show IsUnit (IsLocalRing.residue W (f.derivative.eval a₀))
    rw [hderiv_eval, map_mul, map_pow, ha₀]
    exact (hnW.map (IsLocalRing.residue W)).mul ((hζ₀.isUnit hn.ne').pow (n - 1))

  obtain ⟨a, ha, hamem⟩ := HenselianRing.is_henselian f hmonic a₀ hroot hunit
  have han : a ^ n = 1 := by
    have h := ha.eq_zero
    rwa [heval, sub_eq_zero] at h
  have hres : IsLocalRing.residue W a = ζ₀ := by
    rw [← ha₀]
    exact (Ideal.Quotient.eq).2 hamem
  refine ⟨a, ⟨han, fun l hl => hζ₀.dvd_of_pow_eq_one l ?_⟩⟩
  rw [← hres, ← map_pow, hl, map_one]


-- created on 2026-10-05
