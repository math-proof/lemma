module

public import Def.Data.Vector.Basic
public import Theorem.Nat.EqAddMulDiv

@[expose] public section
open Nat Lean


namespace List.Vector

def transpose (xs : Vector (Vector α n) m) : Vector (Vector α m) n :=
  (range n).map fun j => (range m).map fun i => xs[i][j]

def splitAt {s : List ℕ} (v : Vector α s.prod) (d : ℕ) : Vector (Vector α (s.drop d).prod) (s.take d).prod :=
  -- Inline of List.Prod.eq.MulProdS: that Theorem module imports Theorem.Nat.Mul,
  -- whose public `Comm` clashes with Theorem.Nat.Add pulled in via LengthRange.
  let v : Vector α ((s.take d).prod * (s.drop d).prod) :=
    cast (by simp [List.prod_take_mul_prod_drop]) v
  v.unflatten

@[app_unexpander map]
meta def map.unexpand : PrettyPrinter.Unexpander
  | `($_ $f:term $s:term) =>
    `($s.$(mkIdent `map) $f)
  | _ =>
    throw ()

end List.Vector

def List.Vector.repeat (x : Vector α n) (m : ℕ) : Vector α (m * n) :=
  (List.Vector.replicate m x).flatten

def List.Vector.resize [Zero α] (x : Vector α n) (n' : ℕ) : Vector α n' :=
  cast (congrArg (List.Vector α) (EqAddMulDiv _ _)) (x.repeat (n' / n) ++ Vector.replicate (n' % n) (0 : α))

