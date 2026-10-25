import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section LevelMap

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

theorem pow_le_comap_pow (h : I.map f ≤ J) (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono h n

end LevelMap
end AdicCompletion
