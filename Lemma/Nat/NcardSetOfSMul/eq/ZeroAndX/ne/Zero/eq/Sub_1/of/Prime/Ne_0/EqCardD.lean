import Mathlib
import sympy.Basic


/--
[IsAddCyclic_ncard_setOf_nsmul_eq_zero_and_ne_zero_of_prime_dvd_card](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAddCyclic_ncard_setOf_nsmul_eq_zero_and_ne_zero_of_prime_dvd_card.lean)
-/
@[main]
private lemma main
  [AddCommGroup D] [IsAddCyclic D]
  {m : ℕ}
  {ℓ : ℕ}
-- given
  (hm : Nat.card D = m)
  (hm0 : m ≠ 0)
  (hℓ : ℓ.Prime)
  (hℓm : ℓ ∣ m) :
-- imply
  {x : D | ℓ • x = 0 ∧ x ≠ 0}.ncard = ℓ - 1 := by
-- proof
  classical
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hm]; exact hm0)
  let : Fintype D := Fintype.ofFinite D
  have hcard : Fintype.card D = m := by rw [← Nat.card_eq_fintype_card]; exact hm
  have hset : {x : D | ℓ • x = 0 ∧ x ≠ 0} = {x : D | addOrderOf x = ℓ} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hd : addOrderOf x ∣ ℓ := addOrderOf_dvd_of_nsmul_eq_zero h1
      rcases (Nat.dvd_prime hℓ).mp hd with h | h
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) h2
      · exact h
    · intro h
      refine ⟨?_, ?_⟩
      · rw [← h]; exact addOrderOf_nsmul_eq_zero x
      · intro hx
        rw [hx, addOrderOf_zero] at h
        exact hℓ.one_lt.ne h
  rw [hset]
  have hℓD : ℓ ∣ Fintype.card D := by rw [hcard]; exact hℓm
  have key := IsAddCyclic.card_addOrderOf_eq_totient (α := D) hℓD
  rw [Nat.totient_prime hℓ] at key
  rw [← key, Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp


-- created on 2026-10-05
