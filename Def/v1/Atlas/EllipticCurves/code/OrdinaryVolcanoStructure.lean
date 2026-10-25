/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryVolcanoStructure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.EllipticCurves.code.IsogenyVolcano.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyVolcano
import Structure.v1.Atlas.EllipticCurves.code.OrdinaryVolcanoStructure


noncomputable section

open VolcanoStructure

namespace OrdinaryVolcanoStructure

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

end OrdinaryVolcanoStructure
end
