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
import Structure.v1.Atlas.EllipticCurves.code.RingClassField.Part3
open NumberField

open Elliptic_Curves


namespace ImagQuadPrimeSplitting

open Elliptic_Curves

/-- Roots in `ZMod p` of the minimal polynomial of `ω = (D + √D)/2` (or
`√D`) for the imaginary quadratic discriminant `D`. -/
noncomputable def rootsMinPolyMod (D : ℤ) (p : ℕ) [Fact (Nat.Prime p)] : Finset (ZMod p) :=
  if D % 4 = 1 then
    Finset.univ.filter (fun x : ZMod p => x ^ 2 - x + ((1 - D) / 4 : ℤ) = 0)
  else
    Finset.univ.filter (fun x : ZMod p => x ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0)

/-- The number of `𝒪_K`-ideals of norm `p`, counted by the roots of the
minimal polynomial of `ω` modulo `p`. -/
noncomputable def numIdealsOfNorm (D : ℤ) (p : ℕ) [Fact (Nat.Prime p)] : ℤ :=
  (rootsMinPolyMod D p).card

/-- The prime ideal `𝔭 = (p, ω - r)` in `ℤ[√d]` above a rational prime `p`
and a root `r` of `x² + d ≡ 0 mod p`, used in Lemma 21.6. -/
def primeIdealAbove (p : ℕ) (r : ℤ) : Ideal (ℤ√d) :=
  Ideal.span {(p : ℤ√d), (⟨-r, 1⟩ : ℤ√d)}

end ImagQuadPrimeSplitting
