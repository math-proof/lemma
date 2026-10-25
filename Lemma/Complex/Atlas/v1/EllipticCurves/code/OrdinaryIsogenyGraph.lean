import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.EllipticCurves.code.OrdinaryIsogenyGraph
open VolcanoStructure OrdinaryIsogenyGraph


namespace OrdinaryIsogenyGraph

/--
[crater_degree_eq_jacobi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryIsogenyGraph.lean)
-/
@[path]
lemma crater_degree_eq_jacobi
  {C : OrdinaryIsogenyComponent}
  {K : KohelVolcano C}
  {v : K.volcano.V}
-- given
  (hv : K.volcano.isSurface v) :
-- imply
  (K.volcano.craterGraph.degree v : ℤ) = 1 + jacobiSym C.D₀ C.ℓ :=
-- proof
  crater_degree_eq_jacobiSym K v hv

end OrdinaryIsogenyGraph

namespace OrdinaryIsogenyGraph

/--
[surface_conductor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryIsogenyGraph.lean)
-/
@[path]
lemma surface_conductor
  {C : OrdinaryIsogenyComponent}
  {K : KohelVolcano C}
  {v : K.volcano.V}
-- given
  (hv : (K.volcano.level v : ℕ) = 0) :
-- imply
  K.conductor v = C.f₀ :=
-- proof
  surface_conductor_eq K v hv

end OrdinaryIsogenyGraph

namespace OrdinaryIsogenyGraph

/--
[floor_conductor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinaryIsogenyGraph.lean)
-/
@[path]
lemma floor_conductor
  {C : OrdinaryIsogenyComponent}
  {K : KohelVolcano C}
  {v : K.volcano.V}
-- given
  (hv : (K.volcano.level v : ℕ) = K.volcano.depth) :
-- imply
  K.conductor v = C.f₀ * C.ℓ ^ K.volcano.depth :=
-- proof
  floor_conductor_eq K v hv
end OrdinaryIsogenyGraph



-- created on 2026-10-23
