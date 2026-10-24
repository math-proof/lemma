import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Stirling
open MetaMathlibExt


namespace MetaMathlibExt

/--
[natCardOption](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma natCardOption (α : Type*) [Finite α] :
  Nat.card (Option α) = Nat.card α + 1 := by
  let finiteType : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Nat.card_eq_fintype_card]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cycleQuotientCount_decomposeFin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma cycleQuotientCount_decomposeFin_zero {n : ℕ}
  (e : Equiv.Perm (Fin n)) :
  cycleQuotientCount (Equiv.Perm.decomposeFin.symm (0, e)) =
    cycleQuotientCount e + 1 := by
  rw [cycleQuotientCount, cycleQuotientCount,
    Nat.card_congr (decomposeFinZeroQuotientEquiv e), natCardOption]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cycleQuotientCount_decomposeFin_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma cycleQuotientCount_decomposeFin_succ {n : ℕ} (q : Fin n)
  (e : Equiv.Perm (Fin n)) :
  cycleQuotientCount (Equiv.Perm.decomposeFin.symm (q.succ, e)) =
    cycleQuotientCount e :=
Nat.card_congr (decomposeFinQuotientEquiv q e)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_perm_qcycle_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma card_perm_qcycle_zero (k : ℕ) :
  Fintype.card {σ : Equiv.Perm (Fin 0) // cycleQuotientCount σ = k} =
    Nat.stirlingFirst 0 k := by
  classical
  simp only [cycleQuotientCount_eq]
  have hσ (σ : Equiv.Perm (Fin 0)) : Multiset.card σ.cycleType = 0 := by
    rw [Subsingleton.elim σ 1]
    simp
  simp_rw [hσ]
  cases k <;> simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_perm_qcycle_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma card_perm_qcycle_succ_succ (n k : ℕ) :
  Fintype.card {σ : Equiv.Perm (Fin (n + 1)) //
    cycleQuotientCount σ = k + 1} =
    n * Fintype.card {σ : Equiv.Perm (Fin n) //
      cycleQuotientCount σ = k + 1} +
    Fintype.card {σ : Equiv.Perm (Fin n) // cycleQuotientCount σ = k} := by
  classical
  let split :
    {σ : Equiv.Perm (Fin (n + 1)) // cycleQuotientCount σ = k + 1} ≃
      {pe : Fin (n + 1) × Equiv.Perm (Fin n) //
        cycleQuotientCount (Equiv.Perm.decomposeFin.symm pe) = k + 1} :=
    Equiv.subtypeEquiv Equiv.Perm.decomposeFin (fun σ => by simp)
  let zeroPart :
    {e : Equiv.Perm (Fin n) //
      cycleQuotientCount (Equiv.Perm.decomposeFin.symm (0, e)) = k + 1} ≃
      {e : Equiv.Perm (Fin n) // cycleQuotientCount e = k} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun e => by
      change cycleQuotientCount (Equiv.Perm.decomposeFin.symm (0, e)) = k + 1 ↔
        cycleQuotientCount e = k
      rw [cycleQuotientCount_decomposeFin_zero]
      omega)
  let succPart (q : Fin n) :
    {e : Equiv.Perm (Fin n) //
      cycleQuotientCount (Equiv.Perm.decomposeFin.symm (q.succ, e)) = k + 1} ≃
      {e : Equiv.Perm (Fin n) // cycleQuotientCount e = k + 1} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun e => by
      change cycleQuotientCount (Equiv.Perm.decomposeFin.symm (q.succ, e)) = k + 1 ↔
        cycleQuotientCount e = k + 1
      rw [cycleQuotientCount_decomposeFin_succ])
  rw [Fintype.card_congr split,
    Fintype.card_congr (subtypeProdEquivSigma fun pe =>
      cycleQuotientCount (Equiv.Perm.decomposeFin.symm pe) = k + 1),
    Fintype.card_sigma, Fin.sum_univ_succ, Fintype.card_congr zeroPart]
  simp_rw [Fintype.card_congr (succPart _)]
  simp [add_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_perm_qcycle_eq_stirlingFirst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma card_perm_qcycle_eq_stirlingFirst (n k : ℕ) :
  Fintype.card {σ : Equiv.Perm (Fin n) // cycleQuotientCount σ = k} =
    Nat.stirlingFirst n k := by
  induction n generalizing k with
  | zero => exact card_perm_qcycle_zero k
  | succ n ih =>
    cases k with
    | zero =>
      rw [show Nat.stirlingFirst (n + 1) 0 = 0 by simp]
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun σ => by
        have hpos : 0 < cycleQuotientCount σ.1 := by
          rw [cycleQuotientCount]
          let _ : Nonempty (Quotient (Equiv.Perm.SameCycle.setoid σ.1)) :=
            ⟨Quotient.mk _ 0⟩
          exact Nat.card_pos
        exact (Nat.ne_of_gt hpos) σ.2⟩
    | succ k =>
      rw [card_perm_qcycle_succ_succ, ih, ih, Nat.stirlingFirst_succ_succ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_perm_cycleCount_eq_stirlingFirst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
lemma card_perm_cycleCount_eq_stirlingFirst
  {n k : ℕ} :
-- imply
  Fintype.card {σ : Equiv.Perm (Fin n) //
    Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = k} =
    Nat.stirlingFirst n k := by
-- proof
  simpa only [cycleQuotientCount_eq] using card_perm_qcycle_eq_stirlingFirst n k

end MetaMathlibExt

/--
[cycleQuotientCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean)
-/
@[path]
private lemma cycleQuotientCount_eq_eq
  [Fintype α] [DecidableEq α]
  {σ : Equiv.Perm α} :
-- imply
  cycleQuotientCount σ =
    Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) := by
-- proof
  apply MetaMathlibExt.cycleQuotientCount_eq σ


-- created on 2026-10-20
-- updated on 2026-10-23
