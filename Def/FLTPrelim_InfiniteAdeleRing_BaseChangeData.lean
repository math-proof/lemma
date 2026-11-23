module

public import Mathlib
public import Class.NumberField_Extension
public import Instance.NumberField_InfiniteAdeleRing_BaseChangeData
public import Structure.NumberField_InfiniteAdeleRing_BaseChangeData

@[expose] public section

open NumberField TensorProduct RingHom

open scoped TensorProduct

namespace FLT.InfiniteAdeleBaseChange

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def evalAlgHom (v : InfinitePlace K) : InfiniteAdeleRing K →ₐ[K] v.Completion where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def tensorPiAlgHom :
    ((InfiniteAdeleRing K) ⊗[K] L) →ₐ[K] ((v : InfinitePlace K) → (v.Completion ⊗[K] L)) :=
  Pi.algHom K (fun v : InfinitePlace K => v.Completion ⊗[K] L)
    fun v => Algebra.TensorProduct.map (evalAlgHom K v) (AlgHom.id K L)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in

def tensorPiAlgEquiv [NumberField K] :
    ((InfiniteAdeleRing K) ⊗[K] L) ≃ₐ[K] ((v : InfinitePlace K) → (v.Completion ⊗[K] L)) :=
  AlgEquiv.ofBijective (tensorPiAlgHom K L) (tensorPiAlgHom_bijective K L)

def collapsePlaces :
    ((v : InfinitePlace K) → ((w : v.Extension L) → w.1.Completion)) ≃+*
      InfiniteAdeleRing L where
  toFun x w := x (w.comap (algebraMap K L)) ⟨w, rfl⟩
  invFun y v w := y w.1
  left_inv x := by
    funext v w
    obtain ⟨w, rfl⟩ := w
    rfl
  right_inv y := by funext w; rfl
  map_mul' x y := rfl
  map_add' x y := rfl

variable {K L}

namespace InfinitePlaceData

variable (D : InfinitePlaceData K L)

section Derived

variable [NumberField K]

def baseChangeRingEquiv :
    ((InfiniteAdeleRing K) ⊗[K] L) ≃+* InfiniteAdeleRing L :=
  ((tensorPiAlgEquiv K L).toRingEquiv.trans
    (RingEquiv.piCongrRight fun v => D.placeEquiv v)).trans (collapsePlaces K L)

def conorm : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  D.baseChangeRingEquiv.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom

@[reducible] def adeleAlgebra : Algebra (InfiniteAdeleRing K) (InfiniteAdeleRing L) :=
  D.conorm.toAlgebra

def baseChangeAlgEquiv :
    letI := D.adeleAlgebra
    ((InfiniteAdeleRing K) ⊗[K] L) ≃ₐ[InfiniteAdeleRing K] InfiniteAdeleRing L :=
  letI := D.adeleAlgebra
  AlgEquiv.ofRingEquiv (f := D.baseChangeRingEquiv) (fun x => by
    rw [show algebraMap (InfiniteAdeleRing K) ((InfiniteAdeleRing K) ⊗[K] L) x
        = x ⊗ₜ[K] (1 : L) from rfl]
    rw [D.baseChangeRingEquiv_tmul_one]
    rfl)

end Derived

end InfinitePlaceData

variable (K L)


variable {K L}

def BaseChangeData.ofInfinitePlaceData [NumberField K] (D : InfinitePlaceData K L) :
    letI := D.adeleAlgebra
    BaseChangeData K L :=
  letI := D.adeleAlgebra
  { tensorEquiv := D.baseChangeAlgEquiv
    tensorEquiv_one_tmul := fun l => D.baseChangeAlgEquiv_one_tmul l }

section SelfExtension

variable (K)

def selfPiEquiv (v : InfinitePlace K) :
    ((w : v.Extension K) → w.1.Completion) ≃+* v.Completion :=
  RingEquiv.piUnique fun w : v.Extension K => w.1.Completion

def selfPlaceEquiv (v : InfinitePlace K) :
    (v.Completion ⊗[K] K) ≃+* ((w : v.Extension K) → w.1.Completion) :=
  (Algebra.TensorProduct.rid K K v.Completion).toRingEquiv.trans (selfPiEquiv K v).symm

def selfInfinitePlaceData : InfinitePlaceData K K where
  placeEquiv := selfPlaceEquiv K
  placeEquiv_one_tmul := selfPlaceEquiv_one_tmul K

def selfBaseChangeData [NumberField K] :
    letI := (selfInfinitePlaceData K).adeleAlgebra
    BaseChangeData K K :=
  BaseChangeData.ofInfinitePlaceData (selfInfinitePlaceData K)

end SelfExtension


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

end
