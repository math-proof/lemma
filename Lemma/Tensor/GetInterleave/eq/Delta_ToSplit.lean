import Lemma.Fin.OfSplit.eq.Ite_Mul2
import Lemma.Fin.ToSplit.eq.Ite_Div_2
import Lemma.Nat.Delta_OfSplit.eq.Delta_ToSplit
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.Interleave.eq.AppendStackS_Delta
import sympy.functions.special.tensor_functions
open Nat Tensor Fin


@[main]
private lemma main
-- given
  (k j : Fin (d + d)) :
-- imply
  (interleave d)[k][j] = (↑(KroneckerDelta (k : ℕ) (toSplit j : ℕ)) : Tensor ℝ []) := by
-- proof
  simp only [interleave]
  if hk : k < d then
    have hrow := GetAppend.eq.Get.of.Lt (n := d) (m := d) hk ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ))) : Tensor ℝ [])) ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ) + 1)) : Tensor ℝ []))
    have hA := EqGetStack.fin (fun i : Fin d => [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ))) : Tensor ℝ [])) ⟨(k : ℕ), hk⟩
    have hcell := EqGetStack.fin (fun j : Fin (d + d) => (↑(KroneckerDelta (j : ℕ) (2 * (k : ℕ))) : Tensor ℝ [])) j
    have hof : (↑(KroneckerDelta (j : ℕ) (2 * (k : ℕ))) : Tensor ℝ []) = (↑(KroneckerDelta (j : ℕ) (ofSplit k : ℕ)) : Tensor ℝ []) := by
      simp [OfSplit.eq.Ite_Mul2, hk]
    apply (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hrow).trans
    apply (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hA).trans
    apply hcell.trans
    apply hof.trans
    apply congrArg (fun n : ℕ => (↑n : Tensor ℝ []))
    apply Delta_OfSplit.eq.Delta_ToSplit
  else
    have hge : (k : ℕ) ≥ d := Nat.le_of_not_lt hk
    have hrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (m := d) (n := d) hge k.isLt
      ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ))) : Tensor ℝ []))
      ([i < d] [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ) + 1)) : Tensor ℝ []))
    have hk' : (k : ℕ) - d < d := by
      have := k.isLt
      omega
    have hB := EqGetStack.fin (fun i : Fin d => [j < d + d] (↑(KroneckerDelta (j : ℕ) (2 * (i : ℕ) + 1)) : Tensor ℝ [])) ⟨k - d, hk'⟩
    have hcell := EqGetStack.fin (fun j : Fin (d + d) => (↑(KroneckerDelta (j : ℕ) (2 * ((k : ℕ) - d) + 1)) : Tensor ℝ [])) j
    have hof : (↑(KroneckerDelta (j : ℕ) (2 * ((k : ℕ) - d) + 1)) : Tensor ℝ []) = (↑(KroneckerDelta (j : ℕ) (ofSplit k : ℕ)) : Tensor ℝ []) := by
      simp [OfSplit.eq.Ite_Mul2, hk]
    apply (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hrow).trans
    apply (congrArg (fun t : Tensor ℝ [d + d] => t[j]) hB).trans
    apply hcell.trans
    apply hof.trans
    apply congrArg (fun n : ℕ => (n : Tensor ℝ []))
    apply Delta_OfSplit.eq.Delta_ToSplit


-- created on 2026-09-05
