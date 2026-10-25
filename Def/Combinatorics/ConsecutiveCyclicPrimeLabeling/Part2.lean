/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/ConsecutiveCyclicPrimeLabeling.lean -/

import Mathlib.Data.Nat.GCD.Basic
import Instance.Combinatorics.ConsecutiveCyclicPrimeLabeling


namespace MetaMathlibExt

/-- A consecutive cyclic prime labeling of `P_n x P_2`: `0 < n` and the rotation
    of the labels `1, ..., 2 * n` by `offset` along the perimeter order gives
    relatively prime labels to every adjacent pair. If 1 is on `v_i` the order
    runs `v_i, ..., v_n, u_n, ..., u_1, v_1, ..., v_{i - 1}` (and analogously
    from `u_i`); here `offset` is the rotation placing the labels cyclically. -/
def IsConsecutiveCyclicPrimeLabeling (n offset : ℕ) : Prop :=
  0 < n ∧
    ∀ i j : Fin (2 * n),
      LadderAdj n i j → Nat.Coprime (cyclicLabel n offset i) (cyclicLabel n offset j)

end MetaMathlibExt
