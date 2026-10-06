import Mathlib
import sympy.Basic


/--
[ringKrullDim_le_of_ringHom_isIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ringKrullDim_le_of_ringHom_isIntegral.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R]
  {S : Type v} [CommRing S]
  {φ : R →+* S}
-- given
  (hφ : φ.IsIntegral) :
-- imply
  ringKrullDim S ≤ ringKrullDim R := by
-- proof
  letI : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)


-- created on 2026-10-05
