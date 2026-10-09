import Mathlib
import sympy.Basic


/--
[IsArtinianRing_finite_of_finite_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsArtinianRing_finite_of_finite_residueField.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsArtinianRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)] :
-- imply
  Finite R := by
-- proof
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hn
  have h1 : Finite (R ⧸ IsLocalRing.maximalIdeal R) := ‹Finite (IsLocalRing.ResidueField R)›
  have h2 : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  rw [hn, Ideal.zero_eq_bot] at h2
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv


-- created on 2026-10-03
