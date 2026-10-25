import Mathlib
import Class.Mathlib_Algebra_Algebra_Hom
import Def.Mathlib_Topology_Algebra_UniformRing


section

namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
  {β : Type*} [UniformSpace β] [Ring β] [IsUniformAddGroup β] [IsTopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

variable {f}


theorem mapSemialgHom_apply {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f)
    (x : UniformSpace.Completion α) :
    mapSemialgHom f hf x = UniformSpace.Completion.map f x := rfl

theorem mapSemialgHom_coe {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] {f : α →+* β} (hf : UniformContinuous f)
    (a : α) :
    mapSemialgHom f hf.continuous a = f a := by
  rw [mapSemialgHom_apply, map_coe hf]

end UniformSpace.Completion
end
