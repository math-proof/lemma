import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[fuss_catalan_dvd_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FussCatalanDivisibility.lean)
-/
@[path]
lemma fuss_catalan_dvd_choose
  {a n : ℕ}
-- given
  (ha : 2 ≤ a)
  (hn : 1 ≤ n) :
-- imply
  (a - 1) * n + 1 ∣ Nat.choose (a * n) n := by
-- proof
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : 2 + c - 1 = c + 1 := by omega
  have hdivisor : (2 + c - 1) * (1 + k) + 1 = (c + 1) * (k + 1) + 1 := by
    rw [hsub]; ring
  have hprod : (2 + c) * (1 + k) = ((c + 1) * (k + 1) + 1) + k := by ring
  rw [hdivisor, hprod]
  have hident : Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1) * (k + 1)
    = Nat.choose ((c + 1) * (k + 1) + 1 + k) k * ((c + 1) * (k + 1) + 1) := by
    have h := Nat.choose_succ_right_eq ((c + 1) * (k + 1) + 1 + k) k
    rwa [Nat.add_sub_cancel] at h
  have hgoal_eq : Nat.choose (((c + 1) * (k + 1) + 1) + k) (1 + k)
    = Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1) := by
    rw [Nat.add_comm 1 k]
  rw [hgoal_eq]
  have hdiv : (c + 1) * (k + 1) + 1 ∣ (k + 1) * Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1) := by
    refine ⟨Nat.choose ((c + 1) * (k + 1) + 1 + k) k, ?_⟩
    calc (k + 1) * Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1)
      = Nat.choose ((c + 1) * (k + 1) + 1 + k) (k + 1) * (k + 1) := by ring
      _ = Nat.choose ((c + 1) * (k + 1) + 1 + k) k * ((c + 1) * (k + 1) + 1) := hident
      _ = ((c + 1) * (k + 1) + 1) * Nat.choose ((c + 1) * (k + 1) + 1 + k) k := by ring
  have hcop : Nat.Coprime ((c + 1) * (k + 1) + 1) (k + 1) := by
    have h1 : Nat.Coprime (k + 1) (1 + (c + 1) * (k + 1)) :=
      (Nat.coprime_add_mul_right_right (k + 1) 1 (c + 1)).mpr
        (Nat.coprime_one_right (k + 1))
    have h2 : (c + 1) * (k + 1) + 1 = 1 + (c + 1) * (k + 1) := by ring
    rwa [h2]
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdiv

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
