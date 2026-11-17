module

public import Mathlib
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part3

public section

open GLnBuilding


namespace GLnBuilding

/--
[typeA](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLn.lean)
-/
public theorem typeA
  [Field k]
  {n : Nat} :
-- imply
  TypeA n (coxeterMatrixA n) := by
-- proof
  refine ⟨fun i => by simp [coxeterMatrixA], fun i j hij => ?_, fun i j => ?_⟩
  ·
    simp only [coxeterMatrixA, ite_eq_right hij]
    split_ifs with h
    ·
      right
      rfl
    ·
      left
      rfl
  ·
    simp only [coxeterMatrixA]
    split_ifs <;> first | rfl | (exfalso; omega)

end GLnBuilding


-- created on 2026-10-24
