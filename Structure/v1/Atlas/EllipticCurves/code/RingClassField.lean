/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
import Lemma.Complex.Atlas.v1.EllipticCurves.code.CMTorsor
import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2
import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part7
import Def.v1.Atlas.EllipticCurves.code.RingClassField


namespace Elliptic_Curves

/-- A "ring class field prime" for Theorem 21.12 (Deuring): a positive integer
`q > 1` that is coprime to the discriminant `D`, intended to represent a
prime power norm of a prime in the ring class field. -/
structure RingClassFieldPrime (D : ℤ) where
  q : ℕ
  q_pos : 1 < q
  coprime_q_D : Nat.Coprime q D.natAbs

end Elliptic_Curves
