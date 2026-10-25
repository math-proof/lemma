/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Algebra.Lie.WittMultigradedValue
import Def.Combinatorics.Words.PrimitiveWord
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.PeriodicityLemma
import Def.Combinatorics.Words.LyndonWord.Part6
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem length_wittWordPower {α : Type*} (u : List α) (d : ℕ) :
    (wittWordPower u d).length = d * u.length := by
  simp [wittWordPower, List.length_flatten]

theorem wittWordContent_power {r : ℕ} (u : List (Fin r)) (d : ℕ) :
    wittWordContent (wittWordPower u d) = fun i => d * wittWordContent u i := by
  induction d with
  | zero =>
      funext i
      simp [wittWordPower, wittWordContent]
  | succ d ih =>
      rw [show wittWordPower u (d + 1) = u ++ wittWordPower u d by
        simp [wittWordPower, List.replicate_succ]]
      rw [wittWordContent_append, ih]
      funext i
      simp [Nat.succ_mul, add_comm]

theorem wittEq_wordPower_take_of_hasPeriod {α : Type*} {w : List α} {p d : ℕ}
    (hp0 : 0 < p) (hd0 : 0 < d) (hlen : w.length = p * d) (per : w.HasPeriod p) :
    w = wittWordPower (w.take p) d := by
  have hple : p ≤ w.length := by
    rw [hlen]
    exact Nat.le_mul_of_pos_right p hd0
  have htake : (w.take p).length = p := by simp [hple]
  rw [wittWordPower, ← List.ofFn_get (w.take p), ← List.ofFn_fin_repeat]
  apply List.ext_getElem
  · rw [List.length_ofFn]
    rw [hlen, htake, mul_comm]
  · intro i hiw hirhs
    have himod : i % p < (w.take p).length := by
      rw [List.length_take, min_eq_left hple]
      exact Nat.mod_lt i hp0
    have hper := per.getElem?_mod p i w hiw
    have himodw : i % p < w.length := (Nat.mod_lt i hp0).trans_le hple
    have hperval : w[i % p] = w[i] := by
      rw [List.getElem?_eq_getElem himodw, List.getElem?_eq_getElem hiw] at hper
      exact Option.some.inj hper
    rw [List.getElem_ofFn, Fin.repeat_apply]
    calc
      w[i] = w[i % p] := hperval.symm
      _ = (w.take p)[i % p] := (List.getElem_take).symm
      _ = (w.take p).get _ := by
        congr 1
        simp [htake]

end MetaMathlibExt
