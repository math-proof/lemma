/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.PointCounting
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.CMTorsor
public import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
public import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2
public import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part7
public import Def.v1.Atlas.EllipticCurves.code.RingClassField


public section

namespace Elliptic_Curves

/-- A "ring class field prime" for Theorem 21.12 (Deuring): a positive integer
`q > 1` that is coprime to the discriminant `D`, intended to represent a
prime power norm of a prime in the ring class field. -/
structure RingClassFieldPrime (D : ℤ) where
  q : ℕ
  q_pos : 1 < q
  coprime_q_D : Nat.Coprime q D.natAbs

end Elliptic_Curves
