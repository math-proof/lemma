/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/KimballWebbFibonomialCongruence.lean -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

section

-- Helper: projection R = ZMod (p^3) -> K = ZMod p.
private def piHom (p : ℕ) : ZMod (p ^ 3) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by norm_num)) (ZMod p)

private def qFun (p i : ℕ) : ZMod p :=
  (((Nat.fib (i + 1) : ℕ)) : ZMod p) * ((((Nat.fib i : ℕ)) : ZMod p))⁻¹

private def gFun (p : ℕ) (x : ZMod p) : ZMod p :=
  x ^ 2 - x - 1

private def QSet (p rho : ℕ) : Finset (ZMod p) :=
  (Finset.range (rho - 1)).image (fun i => qFun p (i + 1))

private def CSet (p rho : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ \ QSet p rho

private def TFun (p : ℕ) (x : ZMod p) : ZMod p :=
  1 + x⁻¹

private def SDef (p rho : ℕ) : ZMod p :=
  ∑ i ∈ Finset.range (rho - 1),
    (-1 : ZMod p) ^ (i + 1) * ((((Nat.fib (i + 1) : ℕ)) : ZMod p))⁻¹ ^ 2

private def rFun (p j : ℕ) : ZMod (p ^ 3) :=
  (2 * (((Nat.fib (j + 1) : ℕ)) : ZMod (p ^ 3)) - (((Nat.fib j : ℕ)) : ZMod (p ^ 3))) *
    ((((Nat.fib j : ℕ)) : ZMod (p ^ 3)))⁻¹

private def e1Def (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1), rFun p (i + 1)

private def p2Def (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1), (rFun p (i + 1)) ^ 2

private def WDef (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1),
    ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ *
      ((((Nat.fib (rho - (i + 1)) : ℕ)) : ZMod (p ^ 3)))⁻¹

private def SRDef (p rho : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.range (rho - 1),
    (-1 : ZMod (p ^ 3)) ^ (i + 1) * ((((Nat.fib (i + 1) : ℕ)) : ZMod (p ^ 3)))⁻¹ ^ 2
end
end MetaMathlibExt
