import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Int.GeAbs_0
import Lemma.Int.SubAbsS.le.AbsAdd
import Lemma.Nat.Gt.of.Ge.Gt
open Hyperreal Int Nat


private lemma mp
  {x : ℝ*}
-- given
  (h : Infinite x)
  (r : ℝ) :
-- imply
  Infinite (x + r) := by
-- proof
  apply Infinite.of.All_GtAbs
  have h := All_GtAbs.of.Infinite h
  intro ⟨δ, hδ⟩
  have h_r := GeAbs_0 r
  have h := h ⟨|r| + δ, by linarith⟩
  simp at ⊢ h
  have h_ge := SubAbsS.le.AbsAdd x r
  apply Gt.of.Ge.Gt h_ge
  linarith


@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*)
  (r : ℝ) :
-- imply
  Infinite x ↔ Infinite (x + r) := by
-- proof
  constructor <;>
    intro h
  .
    apply mp h
  .
    have h := mp h (-r)
    simp at h
    exact h


-- created on 2025-12-11
