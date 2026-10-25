/-
Copyright (c) 2024 Kevin Buzzard, Ruben Van de Velde, Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Ported from the Imperial College London FLT formalization
(https://github.com/ImperialCollegeLondon/FLT, blueprint §2.5–2.6).
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.ModCases

set_option autoImplicit false

structure FreyPackage where

  a : ℤ

  b : ℤ

  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0

  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p

  hFLT : a ^ p + b ^ p = c ^ p

  hgcdab : gcd a b = 1

  ha4 : (a : ZMod 4) = 3

  hb2 : (b : ZMod 2) = 0

namespace FreyPackage


end FreyPackage
