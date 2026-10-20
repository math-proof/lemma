/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialCoefficient.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

namespace MetaMathlibExt

/-- The b-ary binomial coefficient: for a valid positional base `b` with `2 ≤ b`,
the finite product of ordinary binomial coefficients `Nat.choose n_l k_l` over the
zero-padded base-`b` digits `n_l` of `n` and `k_l` of `k` (via `Nat.digits b`),
i.e. `∏ l, (n_l.choose k_l)` where both digit lists are padded with zeros to their
maximum length. Lexical identity `jis_term_2cbaa34dfe110242e8240dcc`, semantic concept
`jis_sem_53a0802e644cb28ded12d432`, source statement IDs `jis_30db487b6c50b220112654bd`,
`jis_4bca8b14577e811b2884b0f6`, `jis_63c8aaa1ece1935494892283`, `jis_829c8289db89acb73a53c052`,
`jis_86db58debbc80e01008e85bc`, `jis_bf54256f54829f8681d7d1f4`, `jis_e9d8c5a51bab29e334605dbd`,
`jis_fdf241424325af62582196db`. -/
def bAryBinomialCoefficient (b n k : Nat) (hb : 2 ≤ b) : Nat :=
  let _hb := hb
  let dn := Nat.digits b n
  let dk := Nat.digits b k
  let m := max dn.length dk.length
  ((List.range m).map (fun i => Nat.choose (dn.getD i 0) (dk.getD i 0))).foldl (· * ·) 1

/-- `bAryBinomialCoefficient b n k hb` is the product of the digitwise binomial coefficients over
any range of positions `L` covering the base-`b` digits of both `n` and `k`. -/
theorem bAryBinomialCoefficient_eq_prod_getD (b n k : ℕ) (hb : 2 ≤ b) {L : ℕ}
    (hn : (Nat.digits b n).length ≤ L) (hk : (Nat.digits b k).length ≤ L) :
    bAryBinomialCoefficient b n k hb =
      ∏ i ∈ Finset.range L, ((Nat.digits b n).getD i 0).choose ((Nat.digits b k).getD i 0) := by
  rw [bAryBinomialCoefficient, ← List.prod_eq_foldl]
  refine Finset.prod_subset (Finset.range_subset_range.mpr (max_le hn hk)) fun i _ hi => ?_
  rw [Finset.mem_range, not_lt, max_le_iff] at hi
  rw [List.getD_eq_default _ _ hi.1, List.getD_eq_default _ _ hi.2, Nat.choose_self]

end MetaMathlibExt
