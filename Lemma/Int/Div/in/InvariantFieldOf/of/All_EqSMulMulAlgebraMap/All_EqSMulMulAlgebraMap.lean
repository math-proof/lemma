import Mathlib
import sympy.Basic
import Lemma.CerednikDrinfeld.MumfordQuotient
import Lemma.Int.P2MUtil
open CerednikDrinfeld.Mumford


/--
[CerednikDrinfeld_Mumford_div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_Mumford_div_mem_invariantFieldOf_of_smul_eq_algebraMap_mul.lean)
-/
@[path]
private lemma main
  [Field K] [Group G] [CommRing M] [Algebra K M] [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M]
  {Γ : Subgroup G}
  {u : G → K}
  {x y : FractionRing M}
-- given
  (hx : ∀ γ : G, γ ∈ Γ → γ • x = algebraMap K (FractionRing M) (u γ) * x)
  (hy : ∀ γ : G, γ ∈ Γ → γ • y = algebraMap K (FractionRing M) (u γ) * y) :
-- imply
  x / y ∈ invariantFieldOf K G M Γ := by
-- proof
  rw [mem_invariantFieldOf_iff]
  intro γ hγ
  if hu : u γ = 0 then
    have hx0 : x = 0 := by
      have h := hx γ hγ
      rw [hu, map_zero, zero_mul] at h
      exact (smul_eq_zero_iff_eq γ).1 h
    rw [hx0, zero_div, smul_zero]
  else
    have hc : algebraMap K (FractionRing M) (u γ) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K (FractionRing M)).injective).2 hu
    rw [div_eq_mul_inv, smul_mul', smul_inv'', hx γ hγ, hy γ hγ, mul_inv, mul_assoc, mul_left_comm x,
      ← mul_assoc, mul_inv_cancel₀ hc, one_mul]


-- created on 2026-10-24
