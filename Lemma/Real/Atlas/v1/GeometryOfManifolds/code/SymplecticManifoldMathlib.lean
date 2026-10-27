import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticManifoldMathlib.Part2
open SymplecticGeometry
open scoped TensorProduct


namespace SymplecticGeometry

/--
[SymplecticManifold.map_perm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifoldMathlib.lean)
-/
@[path]
lemma SymplecticManifold.map_perm
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {S : SymplecticManifold n E}
  {x : E}
  {v : Fin 2 → E}
  {σ : Equiv.Perm (Fin 2)} :
-- imply
  (S.ω x) (v ∘ σ) = Equiv.Perm.sign σ • (S.ω x) v :=
-- proof
  (S.ω x).map_perm v σ

end SymplecticGeometry

namespace SymplecticGeometry

/--
[SymplecticManifold.isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifoldMathlib.lean)
-/
@[path]
lemma SymplecticManifold.isClosed
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {S : SymplecticManifold n E}
  {x : E} :
-- imply
  extDeriv S.ω x = 0 :=
-- proof
  S.closed x

end SymplecticGeometry

namespace SymplecticGeometry

/--
[SymplecticManifold.isNondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifoldMathlib.lean)
-/
@[path]
lemma SymplecticManifold.isNondegenerate
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {S : SymplecticManifold n E}
  {x : E} :
-- imply
  AlternatingMap.wedgePower ((S.ω x).toAlternatingMap) n ≠ 0 :=
-- proof
  S.nondegenerate x

end SymplecticGeometry


-- created on 2026-10-23
