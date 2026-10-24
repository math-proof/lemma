import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_AtPPackage
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_heckeTorsion_eq_bot_of_eisensteinAnnihilates](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_heckeTorsion_eq_bot_of_eisensteinAnnihilates.lean)
-/
@[path]
private lemma main
  [AddCommGroup Φ] [Module HeckeAlg Φ]
  {S : Finset Nat.Primes}
  {𝔪 : Ideal HeckeAlg}
  {ℓ : Nat.Primes}
-- given
  (hΦ : EisensteinAnnihilates S Φ)
  (hmax : 𝔪.IsMaximal)
  (hℓ : ℓ ∉ S)
  (hne : heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1) ∉ 𝔪) :
-- imply
  heckeTorsion Φ 𝔪 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hne
  calc x = (1 : HeckeAlg) • x := (one_smul _ x).symm
    _ = (y * (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) + i) • x := by rw [hyi]
    _ = y • ((heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • x) + i • x := by
-- proof
      rw [add_smul, mul_smul]
    _ = 0 := by
      rw [hΦ ℓ hℓ x, smul_zero, zero_add,
        (mem_heckeTorsion_iff Φ 𝔪 x).mp hx i hi]


-- created on 2026-10-23
