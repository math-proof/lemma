import Lemma.Hyperreal.InfinitePos.is.All_Gt
import Lemma.Int.EqAbs.of.Gt_0
import Lemma.Nat.Gt.of.Gt.Ge
import Lemma.Real.GtLog_0.of.Gt_1
import Lemma.Real.LeCoeS.is.Le
import Lemma.Real.LtExpS.is.Lt
import Lemma.Real.GtExp_0
open Hyperreal Int Real Nat


@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.InfinitePos ↔ x.exp.InfinitePos := by
-- proof
  constructor
  <;> intro h
  <;> apply InfinitePos.of.All_Gt.pos
  <;> intro ⟨δ, hδ⟩
  <;> simp
  <;> have h := All_Gt.of.InfinitePos.pos h
  ·
    if h_δ : δ > 1 then
      specialize h ⟨δ.log, GtLog_0.of.Gt_1 h_δ⟩
      simp at h
      have h := LtExpS.of.Lt h
      simp at h
      have : ↑(Real.log δ) = log (δ : ℝ*) := by rfl
      rw [this] at h
      have := LogPos.exp_log_eq_abs (by simp; linarith) (x := (δ : ℝ*))
      simp [show LogPos.exp (Log.log (δ : ℝ*)) = Exp.exp (Log.log (δ : ℝ*)) by rfl] at this
      rw [this] at h
      rwa [EqAbs.of.Gt_0 (by simp; linarith)] at h
    else
      simp at h_δ
      have h : x > 0 := by
        by_contra h_x
        simp at h_x
        specialize h ⟨1, by simp⟩
        simp at h
        linarith
      have h := LtExpS.of.Lt h
      simp at h
      apply Gt.of.Gt.Ge h
      apply LeCoeS.of.Le h_δ
  ·
    specialize h ⟨δ.exp, GtExp_0 δ⟩
    apply Lt.of.LtExpS h


-- created on 2025-12-28
