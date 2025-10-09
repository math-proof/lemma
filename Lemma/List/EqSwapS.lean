import stdlib.List
import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.Eq.of.Ge.Ge
open Nat


@[main]
private lemma main
-- given
  (a : List α)
  (i j : ℕ) :
-- imply
  a.swap i j = a.swap j i := by
-- proof
  unfold List.swap
  -- 0       1     2     3   4   5      6     7     8     9    10      11    12  13     14   15   16  17   18   19
  -- h_eq??? h_eq  h_lt? h_i h_j h_lt?? h_j?? h_eq  h_lt? h_i  h_eq_?  h_lt? h_i h_i??? h_eq h_lt h_j h_eq h_lt h_j
  -- 0       0     1     1   3   5      5     5     6     6    9       10    10  13     13   14   15  17   18   19
  split_ifs with h_eq??? h_eq h_lt? h_i h_j h_lt?? h_j?? h_eq h_lt? h_i h_eq_? h_lt? h_i h_i??? h_eq h_lt h_j h_eq h_lt h_j
  ·
    -- 0: h_eq???
    -- 0: h_eq
    rfl
  ·
    -- 1: h_lt?
    -- 1: h_i
    simp_all
  ·
    rfl
  ·
    -- 3: h_j
    simp_all
  ·
    rfl
  ·
    -- 5: h_lt??
    -- 5: h_j??
    -- 5: h_eq
    simp_all
  ·
    -- 6: h_lt?
    -- 6: h_i
    linarith
  ·
    linarith
  ·
    rfl
  ·
    -- 9: h_eq_?
    rfl
  ·
    -- 10: h_lt?
    -- 10: h_i
    linarith
  ·
    rfl
  ·
    rfl
  ·
    -- 13: h_i???
    -- 13: h_eq
    simp_all
  ·
    -- 14: h_lt
    rfl
  ·
    -- 15: h_j
    have h_ge := Ge.of.NotLt h_lt
    have h_ge?? := Ge.of.NotLt h_lt??
    have h_eq := Eq.of.Ge.Ge h_ge h_ge??
    simp_all
  ·
    linarith
  ·
    -- 17: h_eq
    rfl
  ·
    -- 18: h_lt
    rfl
  ·
    -- 19: h_j
    linarith
  ·
    rfl


-- created on 2025-05-16
-- updated on 2025-05-17
