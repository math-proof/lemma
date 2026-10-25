/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryVolcanoStructure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.EllipticCurves.code.IsogenyVolcano.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyVolcano


noncomputable section

open VolcanoStructure

namespace OrdinaryVolcanoStructure

/-- Combinatorial input for the $\ell$-isogeny volcano of an ordinary elliptic curve
$E/\mathbb{F}_q$ (Kohel's Theorem 22.11). It records the prime $\ell \nmid q$, the trace
of Frobenius $t$ (satisfying the strict Hasse bound), the fundamental discriminant
$D_0 < 0$ of the CM order, the prime-to-$\ell$ conductor $f_0$, the global conductor
$f = f_0 \cdot \ell^h$, and the order of the class group acting on the surface. -/
structure OrdinaryCurveData where
  q : ℕ
  ℓ : ℕ
  hℓ_prime : Nat.Prime ℓ
  hℓ_ndvd_q : ¬(ℓ ∣ q)
  t : ℤ
  hHasse : t ^ 2 < 4 * (q : ℤ)
  D₀ : ℤ
  hD₀_neg : D₀ < 0
  f₀ : ℕ
  hf₀_pos : 0 < f₀
  f : ℕ
  hf_pos : 0 < f
  h : ℕ
  conductor_factorization : f = f₀ * ℓ ^ h
  hℓ_ndvd_f₀ : ¬(ℓ ∣ f₀)
  classOrder : ℕ
  hClassOrder_pos : 0 < classOrder

end OrdinaryVolcanoStructure
end
