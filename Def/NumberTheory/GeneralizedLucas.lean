/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean -/

import Mathlib.Algebra.LinearRecurrence
open Finset

/-!
# Shifted-index `k`-generalized Lucas numbers

Source: Herbert Batte and Florian Luca, *On the Largest Prime factor of the
`k`-generalized Lucas numbers*, arXiv `2311.13047v1`, Introduction, subsection
`Background`. For integers `k ≥ 2` the source defines the sequence on integer
indices `n ≥ 2 - k` with `L_0 = 2`, `L_1 = 1`, zeros on `2 - k, …, -1` for
`k ≥ 3`, and `L_n` the sum of the preceding `k` terms for every `n ≥ 2`
(`k = 2` is classical Lucas).

Formalized as `Nat.kGeneralizedLucas`, indexed exactly over the source domain:
the parameter carries `2 ≤ k` and each index carries `2 - k ≤ n`; no values
are assigned below `2 - k`. The engine is `LinearRecurrence.mkSol` of order
`k` with all coefficients `1`, where natural offset `j` corresponds to source
index `(2 - k) + j`.
-/


namespace Nat

/-- Public source-indexed sequence. Requires `2 ≤ k` and restricts to
`2 - k ≤ n`; the value ignores the proofs computationally. -/
def kGeneralizedLucas (k : ℕ) (_hk : 2 ≤ k) (n : ℤ)
    (_h : 2 - (k : ℤ) ≤ n) : ℕ :=
  (⟨k, fun _ => 1⟩ : LinearRecurrence ℕ).mkSol
    (fun i : Fin k => if i.val + 2 = k then 2 else if i.val + 1 = k then 1 else 0)
    ((n - (2 - (k : ℤ))).toNat)

end Nat
