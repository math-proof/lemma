import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.OrdinaryVolcanoStructure
open VolcanoStructure OrdinaryVolcanoStructure


namespace OrdinaryVolcanoStructure

/--
[conductor_at_level](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryVolcanoStructure.lean)
-/
@[path]
lemma conductor_at_level
  {C : OrdinaryCurveData}
  {V : OrdinaryVolcano C}
  {v : V.kohelVolcano.volcano.V} :
-- imply
  V.kohelVolcano.conductor v = C.f₀ * C.ℓ ^ (V.kohelVolcano.volcano.level v : ℕ) :=
-- proof
  V.kohelVolcano.conductor_eq_level v

end OrdinaryVolcanoStructure

namespace OrdinaryVolcanoStructure

/--
[surface_conductor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryVolcanoStructure.lean)
-/
@[path]
lemma surface_conductor
  {C : OrdinaryCurveData}
  {V : OrdinaryVolcano C}
  {v : V.kohelVolcano.volcano.V}
-- given
  (hv : (V.kohelVolcano.volcano.level v : ℕ) = 0) :
-- imply
  V.kohelVolcano.conductor v = C.f₀ :=
-- proof
  VolcanoStructure.surface_conductor_eq V.kohelVolcano v hv

end OrdinaryVolcanoStructure

namespace OrdinaryVolcanoStructure

/--
[floor_conductor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryVolcanoStructure.lean)
-/
@[path]
lemma floor_conductor
  {C : OrdinaryCurveData}
  {V : OrdinaryVolcano C}
  {v : V.kohelVolcano.volcano.V}
-- given
  (hv : (V.kohelVolcano.volcano.level v : ℕ) = V.kohelVolcano.volcano.depth) :
-- imply
  V.kohelVolcano.conductor v = C.f₀ * C.ℓ ^ C.h := by
-- proof
  rw [conductor_at_level V v, hv, V.depth_eq_h]

end OrdinaryVolcanoStructure

namespace OrdinaryVolcanoStructure

/--
[surface_degree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryVolcanoStructure.lean)
-/
@[path]
lemma surface_degree_eq
  {C : OrdinaryCurveData}
  {V : OrdinaryVolcano C} :
-- imply
  (V.kohelVolcano.volcano.surfaceDegree : ℤ) = 1 + jacobiSym C.D₀ C.ℓ :=
-- proof
  V.kohelVolcano.surface_degree_eq
end OrdinaryVolcanoStructure



-- created on 2026-10-23
