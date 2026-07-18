import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Hyperreal.InfiniteNeg.is.All_Lt
import Lemma.Real.AbsExp.eq.Exp
import Lemma.Real.LtExpS.is.Lt
open Hyperreal Real


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.InfiniteNeg.is.InfinitesimalExp |
| comm | Hyperreal.InfinitesimalExp.is.InfiniteNeg |
| mp   | Hyperreal.InfinitesimalExp.of.InfiniteNeg |
| mpr | Hyperreal.InfiniteNeg.of.InfinitesimalExp |
| mp.mt   | Hyperreal.NotInfiniteNeg.of.NotInfinitesimalExp |
| mpr.mt | Hyperreal.NotInfinitesimalExp.of.NotInfiniteNeg |
-/
@[main, comm, mp and, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → -∞ ↔ x.exp → 0 := by
-- proof
  rw [Infinitesimal.is.All_LtAbs]
  have h_rfl : Exp.exp x = x.exp := rfl
  rw [← h_rfl, AbsExp.eq.Exp x, h_rfl]
  rw [InfiniteNeg.is.All_Lt]
  constructor <;>
    intro h
  ·
    intro ⟨δ, hδ⟩
    simp
    have h := h δ.log
    have := LtExpS.of.Lt h
    have h_rlf : Exp.exp x = x.exp := rfl
    simp [h_rlf] at this
    convert this
    have : (Real.log δ : ℝ*) = (log (δ : ℝ*)) := rfl
    rw [this]
    have hδ := Nat.Ne.of.Gt hδ
    have hδ : (δ : ℝ*) ≠ 0 := by simpa
    have hδ := LogPos.exp_log_eq_abs hδ
    simp [show LogPos.exp (Log.log (δ : ℝ*)) = Exp.exp (Log.log (δ : ℝ*)) by rfl] at hδ
    simp [hδ]
    rw [Int.EqAbs.of.Gt_0]
    simpa
  ·
    intro δ
    have h := h ⟨δ.exp, Real.GtExp_0 δ⟩
    simp at h
    apply Lt.of.LtExpS
    rwa [h_rfl]


-- created on 2025-12-25
