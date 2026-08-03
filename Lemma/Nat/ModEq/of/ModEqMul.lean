import Lemma.Nat.ModMod_Mul.eq.Mod
import Lemma.Nat.ModEq.is.Mod
open Nat


@[main]
private lemma main
  {x y d n : ℕ}
-- given
  (h : x ≡ y [MOD d * n]) :
-- imply
  x ≡ y [MOD n] := by
-- proof
  rw [ModEq.is.Mod]
  rw [← ModMod_Mul.eq.Mod x d n, ← ModMod_Mul.eq.Mod y d n, Mod.of.ModEq h]


@[main]
private lemma left
  {x y d n : ℕ}
-- given
  (h : x ≡ y [MOD d * n]) :
-- imply
  x ≡ y [MOD d] := by
-- proof
  rw [ModEq.is.Mod]
  rw [← ModMod_Mul.eq.Mod x n d, ← ModMod_Mul.eq.Mod y n d]
  have h' : x % (n * d) = y % (n * d) := by
    rw [← Mul.comm d n]
    exact Mod.of.ModEq h
  rw [← h']


-- created on 2026-08-03
