import Lemma.Nat.LeAddS.of.Le.Le
import Lemma.Int.AbsAdd.le.AddAbsS
import Lemma.Hyperreal.Infinite.is.InfiniteNeg
import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Hyperreal.NotInfinite.is.Any_LeAbs
import Lemma.Int.GeAbs_0
import Lemma.Int.SubAbsS.le.AbsAdd
import Lemma.Nat.Add
import Lemma.Nat.Gt.of.Ge.Gt
open Hyperreal Int Nat


private lemma mpr
  {a b : ℝ*}
-- given
  (h_a : ¬Infinite a)
  (h_b : Infinite (a + b)) :
-- imply
  Infinite b := by
-- proof
  contrapose! h_b
  apply NotInfinite.of.Any_LeAbs
  let ⟨⟨δ_a, hδ_a⟩, h_a⟩ := Any_LeAbs.of.NotInfinite h_a
  let ⟨⟨δ_b, hδ_b⟩, h_b⟩ := Any_LeAbs.of.NotInfinite h_b
  use ⟨δ_a + δ_b, by linarith⟩
  calc
    _ ≤ _ := AbsAdd.le.AddAbsS a b
    _ ≤ _ := by
      simp
      apply LeAddS.of.Le.Le
      repeat simpa


private lemma mp
  {x r : ℝ*}
-- given
  (h : Infinite x)
  (h_r : ¬Infinite r) :
-- imply
  Infinite (x + r) := by
-- proof
  have h_r := NotInfiniteNeg.of.NotInfinite h_r
  have h_r := mpr h_r (b := x + r)
  simp at h_r
  apply h_r h


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite |
| comm | Hyperreal.InfiniteAdd.is.Infinite.of.NotInfinite |
| mp   | Hyperreal.InfiniteAdd.of.Infinite.NotInfinite |
| mpr  | Hyperreal.Infinite.of.InfiniteAdd.NotInfinite |
| mp.mt | Hyperreal.NotInfinite.of.NotInfiniteAdd.NotInfinite |
| mpr.mt | Hyperreal.NotInfiniteAdd.of.NotInfinite.NotInfinite |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x.Infinite)
  (y : ℝ*) :
-- imply
  Infinite y ↔ Infinite (x + y) := by
-- proof
  rw [Add.comm]
  constructor
    <;> intro h'
  ·
    apply mp h' h
  ·
    have h := NotInfiniteNeg.of.NotInfinite h
    have h := mp h' h
    simp at h
    exact h


-- created on 2025-12-19
