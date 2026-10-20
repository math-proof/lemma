/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/NimSumLastPile.lean -/

import Batteries.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.List.Basic

namespace MetaMathlibExt

/-! # Nim-sum of the last pile
-/

/--
A Nim position with preceding piles `preceding` and last pile `last` has
nim-sum zero iff `last` equals the xor of `preceding`.

This is only the nim-sum identity behind the source's corollary. The corollary
itself characterizes P-positions; its game-theoretic content (that nim-sum-zero
positions are exactly the P-positions) is Bouton's theorem,
`MetaMathlibExt.BoutonNim.bouton_nim_p_positions` in
`MathlibExt/GameTheory/BoutonNim.lean`.

Source: Tanya Khovanova and Joshua Xiong, "Nim Fractals," Journal of Integer
Sequences 17 (2014), Article 14.7.8, Corollary (label thm:ppos),
lines 163–165,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Khovanova/khova6.tex
Proves `Wanted` entry `nim_ppos_iff_last_eq_xor_fold`, renamed because it states no
P-position predicate.
-/
theorem nim_sum_eq_zero_iff_last_eq_xor_fold
    (preceding : List Nat) (last : Nat) :
    List.foldl Nat.xor 0 (preceding ++ [last]) = 0 ↔ last = List.foldl Nat.xor 0 preceding := by
  rw [List.foldl_concat, Nat.xor_eq]
  constructor
  · intro h
    have h2 : (List.foldl Nat.xor 0 preceding) ^^^ last
        = (List.foldl Nat.xor 0 preceding) ^^^ (List.foldl Nat.xor 0 preceding) := by
      rw [h, Nat.xor_self]
    exact Nat.xor_right_inj.mp h2
  · intro h
    rw [h, Nat.xor_self]

end MetaMathlibExt
