import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
open Hyperreal


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinite.is.InfinitePow |
| comm | Hyperreal.InfinitePow.is.Infinite |
| mp   | Hyperreal.InfinitePow.of.Infinite |
| mpr  | Hyperreal.Infinite.of.InfinitePow |
| mp.mt | Hyperreal.NotInfinite.of.NotInfinitePow |
| mpr.mt | Hyperreal.NotInfinitePow.of.NotInfinite |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [NeZero (n : ℕ)]
-- given
  (x : ℝ*) :
-- imply
  x.Infinite ↔ (x ^ n).Infinite := by
-- proof
  have h_n := NeZero.ne n
  constructor <;>
    intro h
  .
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      simp [pow_succ]
      if h_n : n = 0 then
        subst h_n
        simp_all
      else
        have ih := ih h_n
        apply InfiniteMul.of.Infinite.Infinite ih h
  .
    contrapose! h
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      simp [pow_succ]
      if h_n : n = 0 then
        subst h_n
        simp_all
      else
        have ih := ih h_n
        apply Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite ih h


-- created on 2025-12-16
-- updated on 2025-12-17
