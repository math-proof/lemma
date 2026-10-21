import Mathlib
import Lemma.Fin.RothKroneckerEncode.eq.Add_Mul_RothKroneckerEncode
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothKroneckerEncode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m D : ℕ}
-- given
  (hD : 1 < D)
  {i j : Fin m → ℕ}
  (hi : ∀ h, i h < D)
  (hj : ∀ h, j h < D)
  (heq : rothKroneckerEncode D i = rothKroneckerEncode D j) :
-- imply
  i = j := by
-- proof
  revert D i j hD hi hj heq
  induction m with
  | zero =>
    intro D _ i j _ _ _
    funext h
    exact Fin.elim0 h
  | succ m ih =>
    intro D hD i j hi hj heq
    rw [RothKroneckerEncode.eq.Add_Mul_RothKroneckerEncode,
      RothKroneckerEncode.eq.Add_Mul_RothKroneckerEncode] at heq
    have hzero : i 0 = j 0 := by
      have hmod := congrArg (fun n ↦ n % D) heq
      simpa [Nat.mod_eq_of_lt (hi 0), Nat.mod_eq_of_lt (hj 0)] using hmod
    have htailEq : rothKroneckerEncode D (fun (h : Fin m) ↦ i h.succ) =
        rothKroneckerEncode D (fun (h : Fin m) ↦ j h.succ) := by
      rw [hzero] at heq
      exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hD) (Nat.add_left_cancel heq)
    have htail : (fun (h : Fin m) ↦ i h.succ) = fun (h : Fin m) ↦ j h.succ :=
      ih hD (fun (h : Fin m) ↦ hi h.succ) (fun (h : Fin m) ↦ hj h.succ) htailEq
    funext h
    refine Fin.cases hzero (fun t ↦ ?_) h
    exact congrFun htail t


-- created on 2026-10-21
