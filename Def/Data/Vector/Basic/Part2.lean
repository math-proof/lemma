import Mathlib.Data.Vector.MapLemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lemma.Nat.EqMin_SubMulS
import Lemma.Nat.EqAddMulDiv
import Lemma.List.LengthRange.eq.Length
import Lemma.List.Prod.eq.MulProdS
import Theorem.Algebra.Power.Part2
import Theorem.Function
import Instance.Data.Vector.Basic.Part2
open Nat Lean
open scoped BigOperators


namespace List.Vector

def transpose (xs : Vector (Vector α n) m) : Vector (Vector α m) n :=
  (range n).map fun j => (range m).map fun i => xs[i][j]

def splitAt {s : List ℕ} (v : Vector α s.prod) (d : ℕ) : Vector (Vector α (s.drop d).prod) (s.take d).prod :=
  let v : Vector α ((s.take d).prod * (s.drop d).prod) := cast (by rw [Prod.eq.MulProdS]) v
  v.unflatten

@[app_unexpander map]
def map.unexpand : PrettyPrinter.Unexpander
  | `($_ $f:term $s:term) =>
    `($s.$(mkIdent `map) $f)
  | _ =>
    throw ()

end List.Vector

def List.Vector.repeat (x : Vector α n) (m : ℕ) : Vector α (m * n) :=
  (List.Vector.replicate m x).flatten

def List.Vector.resize [Zero α] (x : Vector α n) (n' : ℕ) : Vector α n' :=
  cast (congrArg (List.Vector α) (EqAddMulDiv _ _)) (x.repeat (n' / n) ++ (0 : Vector α (n' % n)))

