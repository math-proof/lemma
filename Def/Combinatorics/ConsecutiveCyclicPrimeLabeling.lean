/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean -/

import Mathlib.Data.Nat.GCD.Basic


namespace MetaMathlibExt

/-- Perimeter positions of the ladder `P_n x P_2`, identified with `Fin (2 * n)`:
    `0, ..., n - 1` are `v_1, ..., v_n` and `n, ..., 2 * n - 1` are `u_n, ..., u_1`.
    Mbirika et al., JIS Vol. 19: the ladder has horizontal adjacency within each
    row and vertical adjacency between `v_i` and `u_i`. -/
def cyclicLabel (n : ℕ) (offset : ℕ) (i : Fin (2 * n)) : ℕ :=
  ((i.val + offset) % (2 * n)) + 1

/-- Ladder adjacency: perimeter-neighbour edges plus all vertical rung pairs.
    `v_i` sits at index `i - 1` and `u_i` at index `2 * n - i`, so rung pairs
    satisfy `i.val + j.val = 2 * n - 1`. The two corner rungs are also
    perimeter edges. -/
def LadderAdj (n : ℕ) (i j : Fin (2 * n)) : Prop :=
  (((i.val + 1) % (2 * n) = j.val ∨ (j.val + 1) % (2 * n) = i.val) ∨
    i.val + j.val = 2 * n - 1)

end MetaMathlibExt
