/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryVolcanoStructure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.IsogenyVolcano
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

/-- Forget the volcano depth $h$ and conductor factorization in `OrdinaryCurveData` to
recover the underlying `OrdinaryIsogenyComponent` data used by the abstract volcano
formalism. -/
def OrdinaryCurveData.toComponent (C : OrdinaryCurveData) :
    OrdinaryIsogenyComponent where
  q := C.q
  ℓ := C.ℓ
  hℓ_prime := C.hℓ_prime
  hℓ_ndvd_q := C.hℓ_ndvd_q
  t := C.t
  hHasse := C.hHasse
  D₀ := C.D₀
  hD₀_neg := C.hD₀_neg
  f₀ := C.f₀
  hf₀_pos := C.hf₀_pos
  classOrder := C.classOrder
  hClassOrder_pos := C.hClassOrder_pos

/-- Existence statement for the $\ell$-isogeny volcano of an ordinary elliptic curve:
a `KohelVolcano` over the underlying isogeny component whose depth coincides with the
exponent $h$ in the conductor factorization $f = f_0 \cdot \ell^h$. -/
structure OrdinaryVolcano (C : OrdinaryCurveData) where
  kohelVolcano : KohelVolcano C.toComponent
  depth_eq_h : kohelVolcano.volcano.depth = C.h

/-- Existence of the Kohel $\ell$-isogeny volcano for any ordinary elliptic curve
satisfying the input data: there is a `KohelVolcano` whose depth equals the conductor
$\ell$-exponent $h$ (Theorem 22.11). -/
variable {C : OrdinaryCurveData} (V : OrdinaryVolcano C)
