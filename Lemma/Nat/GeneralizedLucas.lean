import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedLucas
open Finset
open Nat


namespace Nat

/--
[kGeneralizedLucas_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
lemma kGeneralizedLucas_zero
  {k : ℕ}
-- given
  (hk : 2 ≤ k)
  (h0 : 2 - (k : ℤ) ≤ 0) :
-- imply
  kGeneralizedLucas k hk 0 h0 = 2 := by
-- proof
  unfold kGeneralizedLucas
  have hoff : ((0 : ℤ) - (2 - (k : ℤ))).toNat = k - 2 := by omega
  rw [hoff]
  have hmem : k - 2 < k := by omega
  have hcore :=
    LinearRecurrence.mkSol_eq_init (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ)
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      ⟨k - 2, hmem⟩
  have hgoal :
    (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      (k - 2) =
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
        ⟨k - 2, hmem⟩ := hcore
  rw [hgoal]
  have h2 : k - 2 + 2 = k := by omega
  change (if k - 2 + 2 = k then (2 : ℕ) else if k - 2 + 1 = k then (1 : ℕ) else (0 : ℕ)) = 2
  exact ite_eq_left h2

end Nat

namespace Nat

/--
[kGeneralizedLucas_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
lemma kGeneralizedLucas_one
  {k : ℕ}
-- given
  (hk : 2 ≤ k)
  (h0 : 2 - (k : ℤ) ≤ 1) :
-- imply
  kGeneralizedLucas k hk 1 h0 = 1 := by
-- proof
  unfold kGeneralizedLucas
  have hoff : ((1 : ℤ) - (2 - (k : ℤ))).toNat = k - 1 := by omega
  rw [hoff]
  have hmem : k - 1 < k := by omega
  have hcore :=
    LinearRecurrence.mkSol_eq_init (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ)
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      ⟨k - 1, hmem⟩
  have hgoal :
    (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      (k - 1) =
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
        ⟨k - 1, hmem⟩ := hcore
  rw [hgoal]
  have hne1 : k - 1 + 2 ≠ k := by omega
  have heq2 : k - 1 + 1 = k := by omega
  change (if k - 1 + 2 = k then (2 : ℕ) else if k - 1 + 1 = k then (1 : ℕ) else (0 : ℕ)) = 1
  rw [ite_eq_right hne1, ite_eq_left heq2]

end Nat

namespace Nat

/--
[kGeneralizedLucas_neg_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
lemma kGeneralizedLucas_neg_eq_zero
  {k : ℕ}
  {n : ℤ}
-- given
  (hk : 3 ≤ k)
  (h : 2 - (k : ℤ) ≤ n)
  (hn : n ≤ -1) :
-- imply
  kGeneralizedLucas k (Nat.le_trans (by decide : 2 ≤ 3) hk) n h = 0 := by
-- proof
  unfold kGeneralizedLucas
  have hnn : 0 ≤ n - (2 - (k : ℤ)) := by omega
  have hto : ((((n - (2 - (k : ℤ))).toNat : ℕ)) : ℤ) = n - (2 - (k : ℤ)) :=
    Int.toNat_of_nonneg hnn
  have hmem : (n - (2 - (k : ℤ))).toNat < k := by omega
  have hcore :=
    LinearRecurrence.mkSol_eq_init (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ)
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      ⟨(n - (2 - (k : ℤ))).toNat, hmem⟩
  have hgoal :
    (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      (n - (2 - (k : ℤ))).toNat =
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
        ⟨(n - (2 - (k : ℤ))).toNat, hmem⟩ := hcore
  rw [hgoal]
  have hne1 : (n - (2 - (k : ℤ))).toNat + 2 ≠ k := by omega
  have hne2 : (n - (2 - (k : ℤ))).toNat + 1 ≠ k := by omega
  change (if (n - (2 - (k : ℤ))).toNat + 2 = k then (2 : ℕ)
    else if (n - (2 - (k : ℤ))).toNat + 1 = k then (1 : ℕ) else (0 : ℕ)) = 0
  rw [ite_eq_right hne1, ite_eq_right hne2]

end Nat

namespace Nat

/--
[kGeneralizedLucas_lower_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
lemma kGeneralizedLucas_lower_zero
  {k : ℕ}
-- given
  (hk : 3 ≤ k)
  (h : 2 - (k : ℤ) ≤ 2 - (k : ℤ)) :
-- imply
  kGeneralizedLucas k (Nat.le_trans (by decide : 2 ≤ 3) hk) (2 - (k : ℤ)) h =
    0 := by
-- proof
  have hn : (2 - (k : ℤ)) ≤ -1 := by omega
  exact kGeneralizedLucas_neg_eq_zero k hk _ h hn

end Nat

namespace Nat

/--
[kGeneralizedLucas_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
lemma kGeneralizedLucas_recurrence
  {k : ℕ}
  {n : ℤ}
-- given
  (hk : 2 ≤ k)
  (hn : 2 ≤ n)
  (h : 2 - (k : ℤ) ≤ n) :
-- imply
  kGeneralizedLucas k hk n h =
    ∑ i : Fin k,
    kGeneralizedLucas k hk ((n - (k : ℤ)) + (i.val : ℤ)) (by omega) := by
-- proof
  have hnn : 0 ≤ n - (2 - (k : ℤ)) := by omega
  have hto : ((((n - (2 - (k : ℤ))).toNat : ℕ)) : ℤ) = n - (2 - (k : ℤ)) :=
    Int.toNat_of_nonneg hnn
  have hm_ge : k ≤ (n - (2 - (k : ℤ))).toNat := by omega
  have hsol_at :=
    LinearRecurrence.is_sol_mkSol (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ)
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      ((n - (2 - (k : ℤ))).toNat - k)
  have hm_eq :
    (n - (2 - (k : ℤ))).toNat - k +
      (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).order =
      (n - (2 - (k : ℤ))).toNat :=
    Nat.sub_add_cancel hm_ge
  rw [hm_eq] at hsol_at
  have hlhs :
    kGeneralizedLucas k hk n h = (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
      (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
      (n - (2 - (k : ℤ))).toNat := rfl
  rw [hlhs, hsol_at]
  apply Finset.sum_congr rfl
  intro i _
  have hcoeff : (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).coeffs i = 1 := rfl
  rw [hcoeff, one_mul]
  have hterm_eq :
    kGeneralizedLucas k hk ((n - (k : ℤ)) + (i.val : ℤ)) (by omega) =
      (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
        (fun j : Fin k => if j.val + 2 = k then 2 else if j.val + 1 = k then 1 else 0)
        ((n - (2 - (k : ℤ))).toNat - k + i.val) := by
    have hilt := i.isLt
    unfold kGeneralizedLucas
    congr 1
    omega
  rw [hterm_eq]

end Nat


-- created on 2026-10-20
-- updated on 2026-10-23
