import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[padicValInt_pow_sub_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ClassicalLte.lean)
-/
@[path]
lemma padicValInt_pow_sub_pow
  {p : ℕ} [Fact (Nat.Prime p)]
  {a b : ℤ}
  {n : ℕ}
-- given
  (hodd : Odd p)
  (hne : a ≠ b)
  (hcop : ¬ (p : ℤ) ∣ a * b)
  (hdiv : (p : ℤ) ∣ a - b)
  (hn : n ≠ 0) :
-- imply
  padicValInt p (a ^ n - b ^ n) = padicValNat p n + padicValInt p (a - b) := by
-- proof
  have hp : Nat.Prime p := Fact.out
  have ha : ¬ (p : ℤ) ∣ a := fun hpa => hcop (dvd_mul_of_dvd_left hpa b)
  have hbase : FiniteMultiplicity (p : ℤ) (a - b) := by
    rw [Int.finiteMultiplicity_iff]
    exact ⟨by simpa using hp.ne_one, sub_ne_zero.mpr hne⟩
  have hnfin : FiniteMultiplicity p n := by
    rw [Nat.finiteMultiplicity_iff]
    exact ⟨hp.ne_one, Nat.pos_of_ne_zero hn⟩
  have hem := Int.emultiplicity_pow_sub_pow hp hodd hdiv ha n
  have hval (z : ℤ) : padicValInt p z = (emultiplicity (p : ℤ) z).toNat := by
    rw [padicValInt, ← Nat.toNat_emultiplicity, Int.emultiplicity_natAbs]
  rw [hval, hval, ← Nat.toNat_emultiplicity]
  rw [hem, ENat.toNat_add
    (finiteMultiplicity_iff_emultiplicity_ne_top.mp hbase)
    (finiteMultiplicity_iff_emultiplicity_ne_top.mp hnfin), add_comm]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
