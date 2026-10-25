/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MultibondReindex
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetReflection
open Finset


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem multibondConfigReindex_cubicalDualVertexZReflect_none
    {a b c : Nat} (s : CubicalDualVertex a b c -> Bool) :
    multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s none =
      s none := rfl

@[simp] theorem multibondConfigReindex_cubicalDualVertexZReflect_some
    {a b c : Nat} (s : CubicalDualVertex a b c -> Bool)
    (q : CubicalCell a b c) :
    multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
        (some (cubicalCellZReflect q)) = s (some q) := by
  change s (some (cubicalCellZReflect (cubicalCellZReflect q))) = s (some q)
  congr 2
  cases q
  simp [cubicalCellZReflect]

@[simp] theorem multibondConfigReindex_cubicalDualVertexZReflect_mk
    {a b c : Nat} (s : CubicalDualVertex a b c -> Bool)
    (x : Fin a) (y : Fin b) (z : Fin c) :
    multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
        (some (⟨x, y, z.rev⟩ : CubicalCell a b c)) =
      s (some ⟨x, y, z⟩) := by
  exact multibondConfigReindex_cubicalDualVertexZReflect_some s ⟨x, y, z⟩

theorem finBackward_rev_map_rev {n : Nat} (k : Fin (n + 1)) :
    (finBackward k.rev).map Fin.rev = finForward k := by
  apply Option.ext
  intro z
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨w, hw, hwz⟩
    apply (finForward_eq_some_iff k z).2
    have hkr := (finBackward_eq_some_iff k.rev w).1 hw
    have hrev := congrArg Fin.rev hkr
    simpa [← hwz, Fin.rev_succ] using hrev
  · intro hz
    have hk := (finForward_eq_some_iff k z).1 hz
    refine ⟨z.rev, ?_, by simp⟩
    apply (finBackward_eq_some_iff k.rev z.rev).2
    rw [hk, Fin.rev_castSucc]

theorem finForward_rev_map_rev {n : Nat} (k : Fin (n + 1)) :
    (finForward k.rev).map Fin.rev = finBackward k := by
  apply Option.ext
  intro z
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨w, hw, hwz⟩
    apply (finBackward_eq_some_iff k z).2
    have hkr := (finForward_eq_some_iff k.rev w).1 hw
    have hrev := congrArg Fin.rev hkr
    simpa [← hwz, Fin.rev_castSucc] using hrev
  · intro hz
    have hk := (finBackward_eq_some_iff k z).1 hz
    refine ⟨z.rev, ?_, by simp⟩
    apply (finForward_eq_some_iff k.rev z.rev).2
    rw [hk, Fin.rev_succ]

theorem multibondConfigReindex_cubicalDualVertexZReflect_optionMap
    {a b c : Nat} (s : CubicalDualVertex a b c -> Bool)
    (x : Fin a) (y : Fin b) (o : Option (Fin c)) :
    multibondConfigReindex (cubicalDualVertexZReflectEquiv a b c) s
        (o.map fun z => (⟨x, y, z⟩ : CubicalCell a b c)) =
      s (o.map fun z => (⟨x, y, z.rev⟩ : CubicalCell a b c)) := by
  cases o with
  | none => rfl
  | some z =>
      change multibondConfigReindex
          (cubicalDualVertexZReflectEquiv a b c) s (some ⟨x, y, z⟩) =
        s (some ⟨x, y, z.rev⟩)
      simpa using
        (multibondConfigReindex_cubicalDualVertexZReflect_mk s x y z.rev)


end
end StatMech.FrontierA
