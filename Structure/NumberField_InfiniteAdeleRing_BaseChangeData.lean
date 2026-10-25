import Mathlib
import Class.NumberField_Extension
import Instance.NumberField_InfiniteAdeleRing_BaseChangeData

open NumberField TensorProduct

open scoped TensorProduct

namespace FLT.InfiniteAdeleBaseChange

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]


structure InfinitePlaceData where

  placeEquiv (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) ≃+* ((w : v.Extension L) → w.1.Completion)

  placeEquiv_one_tmul (v : InfinitePlace K) (l : L) (w : v.Extension L) :
    placeEquiv v ((1 : v.Completion) ⊗ₜ[K] l) w = algebraMap L w.1.Completion l


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in


variable {K L}

namespace InfinitePlaceData

variable (D : InfinitePlaceData K L)

section Derived

variable [NumberField K]


end Derived

end InfinitePlaceData

variable (K L)

structure BaseChangeData [NumberField K]
    [Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L)] where

  tensorEquiv : ((InfiniteAdeleRing K) ⊗[K] L) ≃ₐ[InfiniteAdeleRing K] InfiniteAdeleRing L

  tensorEquiv_one_tmul (l : L) :
    tensorEquiv ((1 : InfiniteAdeleRing K) ⊗ₜ[K] l) = algebraMap L (InfiniteAdeleRing L) l

variable {K L}


section SelfExtension

variable (K)


end SelfExtension

section Gates


end Gates

end

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeRingEquiv_one_tmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms InfinitePlaceData.baseChangeRingEquiv_one_tmul

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.conorm_algebraMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms InfinitePlaceData.conorm_algebraMap

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeRingEquiv_tmul_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms InfinitePlaceData.baseChangeRingEquiv_tmul_one

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeAlgEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms InfinitePlaceData.baseChangeAlgEquiv

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeAlgEquiv_one_tmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms InfinitePlaceData.baseChangeAlgEquiv_one_tmul

/--
info: 'FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms tensorPiAlgHom_bijective

/--
info: 'FLT.InfiniteAdeleBaseChange.collapsePlaces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms collapsePlaces

/--
info: 'FLT.InfiniteAdeleBaseChange.BaseChangeData.ofInfinitePlaceData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BaseChangeData.ofInfinitePlaceData

/--
info: 'FLT.InfiniteAdeleBaseChange.selfInfinitePlaceData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms selfInfinitePlaceData

/--
info: 'FLT.InfiniteAdeleBaseChange.selfBaseChangeData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms selfBaseChangeData

/--
info: 'FLT.InfiniteAdeleBaseChange.gate_baseChangeRingEquiv_separates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms gate_baseChangeRingEquiv_separates

/--
info: 'FLT.InfiniteAdeleBaseChange.gate_conorm_self_fixes_principal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms gate_conorm_self_fixes_principal

/--
info: 'FLT.InfiniteAdeleBaseChange.gate_conorm_separates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms gate_conorm_separates

end FLT.InfiniteAdeleBaseChange
