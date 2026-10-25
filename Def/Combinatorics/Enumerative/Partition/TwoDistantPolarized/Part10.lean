/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part9


namespace MetaMathlibExt.TwoDistantPolarized

open List

def Bset (n : ℕ) := {p : Nat.Partition n //
  p.parts.Nodup ∧ ∀ e ∈ p.parts, e % 2 = 0 → 2 * (p.parts.filter (fun i => i % 2 = 1)).card < e}

noncomputable def e2 (n : ℕ) : Omega n ≃ Bset n where
  toFun y := ⟨ofList (polyParts y.1) (polyParts_pos y.1) (by rw [sum_polyParts]; exact y.2.2),
    polyParts_polarized y.1 y.2.1⟩
  invFun x := ⟨invB x.1, invB_pairwise x.1, invB_sum x.1 x.2.1 x.2.2⟩
  left_inv y := by
    apply Subtype.ext
    dsimp only
    exact invB_of_parts _ y.1 y.2.1 rfl
  right_inv x := by
    apply Subtype.ext
    apply Nat.Partition.ext
    dsimp only
    exact polyParts_invB x.1 x.2.1 x.2.2

end MetaMathlibExt.TwoDistantPolarized
