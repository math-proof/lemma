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

instance decidableLadderAdj (n : ℕ) (i j : Fin (2 * n)) :
    Decidable (LadderAdj n i j) := by
  unfold LadderAdj
  infer_instance

/-- A consecutive cyclic prime labeling of `P_n x P_2`: `0 < n` and the rotation
    of the labels `1, ..., 2 * n` by `offset` along the perimeter order gives
    relatively prime labels to every adjacent pair. If 1 is on `v_i` the order
    runs `v_i, ..., v_n, u_n, ..., u_1, v_1, ..., v_{i - 1}` (and analogously
    from `u_i`); here `offset` is the rotation placing the labels cyclically. -/
def IsConsecutiveCyclicPrimeLabeling (n offset : ℕ) : Prop :=
  0 < n ∧
    ∀ i j : Fin (2 * n),
      LadderAdj n i j → Nat.Coprime (cyclicLabel n offset i) (cyclicLabel n offset j)

instance decidableIsConsecutiveCyclicPrimeLabeling (n offset : ℕ) :
    Decidable (IsConsecutiveCyclicPrimeLabeling n offset) := by
  unfold IsConsecutiveCyclicPrimeLabeling LadderAdj Nat.Coprime
  infer_instance
end MetaMathlibExt
