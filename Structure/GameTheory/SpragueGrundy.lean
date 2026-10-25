/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Lattice.Nat


namespace MetaMathlibExt.SpragueGrundy

/-- Finite impartial game with a strictly decreasing natural rank.

Finite move sets plus a strictly decreasing natural rank give a finite
reachable game tree from any starting position, even if `Pos` contains
unreachable points: every move strictly decreases `rank`, so every play
terminates and only finitely many positions are reachable.
-/
structure ImpartialGame where
  Pos : Type
  eqDec : DecidableEq Pos
  moves : Pos → Finset Pos
  rank : Pos → ℕ
  rank_lt : ∀ p q, q ∈ moves p → rank q < rank p
  start : Pos

end MetaMathlibExt.SpragueGrundy
