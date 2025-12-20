import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.Infinitesimal
import Lemma.Nat.Mul
open Hyperreal Nat


@[main, comm, mp, mpr]
private lemma main
  [NeZero (n : ℕ)]
-- given
  (x : ℝ*) :
-- imply
  Infinitesimal x ↔ Infinitesimal (x ^ n) := by
-- proof
  have h_n := NeZero.ne n
  constructor <;>
    intro h
  .
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      if h_n : n = 0 then
        subst h_n
        simpa
      else
        have ih := ih h_n
        have := InfinitesimalMul.of.Infinitesimal.Infinitesimal h ih
        grind
  .
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      if h_n : n = 0 then
        subst h_n
        simp at h
        assumption
      else
        rw [pow_succ] at h
        by_contra h_x
        rw [Mul.comm] at h
        have h := Infinitesimal.of.InfinitesimalMul.NotInfinitesimal h_x h
        have ih := ih h_n h
        have := InfinitesimalMul.of.Infinitesimal.Infinitesimal h ih
        grind


-- created on 2025-12-11
-- updated on 2025-12-20
