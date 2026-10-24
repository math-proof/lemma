/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/GandhiNthPrimeFormula.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open scoped BigOperators

namespace MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted

/-- Fiber finset over `m`: pairs `(d, m/d - 1)` for `d ∣ P`, `d ∣ m` (empty if `m = 0`). -/
private def gandhiFiber (P m : ℕ) : Finset (↥P.divisors × ℕ) :=
  if m = 0 then ∅
  else ((P.divisors.filter (· ∣ m)).attach.image
    (fun d => ((⟨d.1, (Finset.mem_filter.mp d.2).1⟩, m / d.1 - 1) : ↥P.divisors × ℕ)))

/-- Membership in the fiber finset. -/
private theorem gandhiFiber_mem (P m : ℕ) (p : ↥P.divisors × ℕ) :
    p ∈ gandhiFiber P m ↔ m ≠ 0 ∧ p.1.1 ∣ m ∧ p.2 = m / p.1.1 - 1 := by
  unfold gandhiFiber
  split_ifs with hm
  · subst hm
    simp
  · rw [Finset.mem_image]
    constructor
    · rintro ⟨d, _, hdp⟩
      have h1 : ((⟨d.1, (Finset.mem_filter.mp d.2).1⟩ : ↥P.divisors)) = p.1 :=
        congrArg Prod.fst hdp
      have h2 : m / d.1 - 1 = p.2 := congrArg Prod.snd hdp
      have hd_eq : d.1 = p.1.1 := congrArg Subtype.val h1
      obtain ⟨-, hdivm⟩ := Finset.mem_filter.mp d.2
      refine ⟨hm, hd_eq ▸ hdivm, ?_⟩
      rw [hd_eq] at h2
      exact h2.symm
    · rintro ⟨-, hdiv, hk⟩
      refine ⟨⟨p.1.1, Finset.mem_filter.mpr ⟨p.1.2, hdiv⟩⟩,
        Finset.mem_attach _ _, Prod.ext (Subtype.ext rfl) hk.symm⟩

/-- Every pair lies in the fiber over its product. -/
private theorem gandhiFiber_self_mem (P : ℕ) (p : ↥P.divisors × ℕ) :
    p ∈ gandhiFiber P (p.1.1 * (p.2 + 1)) := by
  rw [gandhiFiber_mem]
  have hpos : 0 < p.1.1 := Nat.pos_of_mem_divisors p.1.2
  refine ⟨mul_ne_zero (ne_of_gt hpos) (by omega), dvd_mul_right _ _, ?_⟩
  rw [mul_comm p.1.1 (p.2 + 1), Nat.mul_div_cancel (p.2 + 1) hpos, Nat.add_sub_cancel]

/-- Points in a nonzero fiber project back to the fiber index. -/
private theorem gandhiFiber_proj (P : ℕ) (m : ℕ) (hm : m ≠ 0) (p : ↥P.divisors × ℕ)
    (hpm : p ∈ gandhiFiber P m) : p.1.1 * (p.2 + 1) = m := by
  rw [gandhiFiber_mem] at hpm
  obtain ⟨-, hdiv, hk⟩ := hpm
  have hpos : 0 < p.1.1 := Nat.pos_of_mem_divisors p.1.2
  have hle : 1 ≤ m / p.1.1 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv) hpos
  have hkk : p.2 + 1 = m / p.1.1 := by omega
  rw [hkk]
  exact Nat.mul_div_cancel' hdiv

/-- The equivalence between the sigma of fibers and the product. -/
private def gandhiEquiv (P : ℕ) : (Σ m : ℕ, ↥(gandhiFiber P m)) ≃ (↥P.divisors × ℕ) where
  toFun q := q.2.1
  invFun p := ⟨p.1.1 * (p.2 + 1), ⟨p, gandhiFiber_self_mem P p⟩⟩
  left_inv := by
    rintro ⟨m, p, hpm⟩
    rcases eq_or_ne m 0 with rfl | hm
    · have hS : gandhiFiber P 0 = ∅ := by simp [gandhiFiber]
      rw [hS] at hpm
      exact (Finset.notMem_empty p hpm).elim
    · have hFm : p.1.1 * (p.2 + 1) = m := gandhiFiber_proj P m hm p hpm
      subst hFm
      rfl
  right_inv := fun p => rfl
end MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted
