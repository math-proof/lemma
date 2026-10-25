import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
open TriangularDecomposition


namespace TriangularDecomposition

/--
[weightSubspace_eq_mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma weightSubspace_eq_mathlib
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {Δ : TriangularDecomposition R 𝔤}
  {μ : Δ.𝔥 →ₗ[R] R} :
-- imply
  Δ.weightSubspace M μ = (LieModule.weightSpace (R := R) (L := Δ.𝔥) M (μ ·)).toSubmodule := by
-- proof
  ext m
  constructor
  ·
    intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace]
    intro x; exact hm x
  ·
    intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace] at hm
    intro h; exact hm h

end TriangularDecomposition


-- created on 2026-10-23
-- updated on 2026-10-24
