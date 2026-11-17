/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/KimballWebbFibonomialCongruence.lean -/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Int.Fib.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

-- Helper: projection R = ZMod (p^3) -> K = ZMod p.
def piHom (p : ℕ) : ZMod (p ^ 3) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by norm_num)) (ZMod p)

def qFun (p i : ℕ) : ZMod p :=
  (((Nat.fib (i + 1) : ℕ)) : ZMod p) * ((((Nat.fib i : ℕ)) : ZMod p))⁻¹

def gFun (p : ℕ) (x : ZMod p) : ZMod p :=
  x ^ 2 - x - 1

def QSet (p rho : ℕ) : Finset (ZMod p) :=
  (Finset.range (rho - 1)).image (fun i => qFun p (i + 1))

def CSet (p rho : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ \ QSet p rho

def TFun (p : ℕ) (x : ZMod p) : ZMod p :=
  1 + x⁻¹

def SDef (p rho : ℕ) : ZMod p :=
  ∑ i ∈ Finset.range (rho - 1),
    (-1 : ZMod p) ^ (i + 1) * ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ ^ 2

def rFun (p j : ℕ) : ZMod (p ^ 3) :=
  (2 * (((Nat.fib (j + 1) : ℕ)) : ZMod (p ^ 3)) - (((Nat.fib j : ℕ)) : ZMod (p ^ 3))) *
    ((((Nat.fib j : ℕ)) : ZMod (p ^ 3)))⁻¹

def e1Def (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1), rFun p (i + 1)

def p2Def (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1), (rFun p (i + 1)) ^ 2

def WDef (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1),
    ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ *
      ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3)))⁻¹

def SRDef (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1),
    (-1 : ZMod (p ^ 3)) ^ (i + 1) * ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ ^ 2

end
end MetaMathlibExt
