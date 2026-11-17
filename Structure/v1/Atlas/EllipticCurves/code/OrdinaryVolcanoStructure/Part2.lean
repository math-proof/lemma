/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryVolcanoStructure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.EllipticCurves.code.IsogenyVolcano.Part3
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.IsogenyVolcano
public import Def.v1.Atlas.EllipticCurves.code.OrdinaryVolcanoStructure


public noncomputable section

open VolcanoStructure

namespace OrdinaryVolcanoStructure

/-- Existence statement for the $\ell$-isogeny volcano of an ordinary elliptic curve:
a `KohelVolcano` over the underlying isogeny component whose depth coincides with the
exponent $h$ in the conductor factorization $f = f_0 \cdot \ell^h$. -/
structure OrdinaryVolcano (C : OrdinaryCurveData) where
  kohelVolcano : KohelVolcano C.toComponent
  depth_eq_h : kohelVolcano.volcano.depth = C.h

end OrdinaryVolcanoStructure
end
