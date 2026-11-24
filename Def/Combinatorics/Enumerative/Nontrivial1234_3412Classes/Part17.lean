module
public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic
public import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part16


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def ntQuads (n : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    (List.range n).flatMap fun c => (List.range n).filterMap fun d =>
      if a < b ∧ b < c ∧ c < d then some (a, b, c, d) else none

def ntHasPatB (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : Bool :=
  q.any fun (a, b, c, d) =>
    let x := s.getD a 0
    let y := s.getD b 0
    let z := s.getD c 0
    let w := s.getD d 0
    (x < y && y < z && z < w) || (z < w && w < x && x < y)

def ntSemiVal (n j i : ℕ) : ℕ :=
  (j + n - 1 - i) % n

def ntInTB (n : ℕ) (s : List ℕ) : Bool :=
  (List.range n).any fun j => (List.range n).any fun p =>
    (List.range n).any fun q => p != q && (List.range n).all fun i =>
      s.getD i 0 == if i = p then ntSemiVal n j q
        else if i = q then ntSemiVal n j p else ntSemiVal n j i

def ntIsGB (n : ℕ) (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : Bool :=
  s.headD 0 != n - 1 && s.getLastD 0 != 0 && ntHasPatB q s && !ntInTB n s

def ntNbrAt (s : List ℕ) (q : ℕ × ℕ × ℕ × ℕ) : Option (List ℕ) :=
  let (a, b, c, d) := q
  let x := s.getD a 0
  let y := s.getD b 0
  let z := s.getD c 0
  let w := s.getD d 0
  if (x < y && y < z && z < w) || (z < w && w < x && x < y) then
    some (((((s.set a z).set c x).set b w).set d y))
  else none

def ntNbrs (q : List (ℕ × ℕ × ℕ × ℕ)) (s : List ℕ) : List (List ℕ) :=
  q.filterMap (ntNbrAt s)

def ntFact : ℕ → ℕ
  | 0 => 1
  | k + 1 => (k + 1) * ntFact k

def ntLehmer : List ℕ → ℕ
  | [] => 0
  | x :: xs => (xs.countP (· < x)) * ntFact xs.length + ntLehmer xs

end MetaMathlibExt
