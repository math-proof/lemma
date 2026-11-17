/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Order.Lattice.Nat


public section

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
