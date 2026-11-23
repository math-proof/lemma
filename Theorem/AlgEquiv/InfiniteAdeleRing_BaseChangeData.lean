module

public import Mathlib
public import Class.NumberField_Extension
public import Instance.NumberField_InfiniteAdeleRing_BaseChangeData
public import Structure.NumberField_InfiniteAdeleRing_BaseChangeData

public noncomputable section

open NumberField TensorProduct RingHom

open scoped TensorProduct

namespace FLT.InfiniteAdeleBaseChange

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]


@[simp] public theorem evalAlgHom_apply (v : InfinitePlace K) (x : InfiniteAdeleRing K) :
    evalAlgHom K v x = x v := rfl


@[simp] public theorem tensorPiAlgHom_tmul_apply (x : InfiniteAdeleRing K) (l : L)
    (v : InfinitePlace K) :
    tensorPiAlgHom K L (x ⊗ₜ[K] l) v = x v ⊗ₜ[K] l := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in


public theorem tensorPiAlgHom_bijective [NumberField K] :
    Function.Bijective (tensorPiAlgHom K L) := by
  classical
  have key : ⇑(tensorPiAlgHom K L) =
      ⇑(AlgEquiv.piCongrRight
          fun v : InfinitePlace K => Algebra.TensorProduct.comm K L v.Completion) ∘
        ⇑(Algebra.TensorProduct.piRight K K L
          fun v : InfinitePlace K => v.Completion) ∘
          ⇑(Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [Function.comp_apply, map_zero]
    | tmul x l =>
      funext v
      show x v ⊗ₜ[K] l = Algebra.TensorProduct.comm K L v.Completion
        ((Algebra.TensorProduct.piRight K K L fun v : InfinitePlace K => v.Completion)
          (Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L (x ⊗ₜ[K] l)) v)

      rfl
    | add z₁ z₂ h₁ h₂ =>
      simp only [Function.comp_apply, map_add] at h₁ h₂ ⊢
      rw [h₁, h₂]
  rw [key]
  exact (AlgEquiv.piCongrRight
      fun v : InfinitePlace K => Algebra.TensorProduct.comm K L v.Completion).bijective.comp
    ((Algebra.TensorProduct.piRight K K L
      fun v : InfinitePlace K => v.Completion).bijective.comp
        (Algebra.TensorProduct.comm K (InfiniteAdeleRing K) L).bijective)


@[simp] public theorem tensorPiAlgEquiv_tmul_apply [NumberField K] (x : InfiniteAdeleRing K) (l : L)
    (v : InfinitePlace K) :
    tensorPiAlgEquiv K L (x ⊗ₜ[K] l) v = x v ⊗ₜ[K] l := rfl


@[simp] public theorem collapsePlaces_apply
    (x : (v : InfinitePlace K) → ((w : v.Extension L) → w.1.Completion))
    (w : InfinitePlace L) :
    collapsePlaces K L x w = x (w.comap (algebraMap K L)) ⟨w, rfl⟩ := rfl


public theorem algebraMap_infiniteAdeleRing_apply (l : L) (w : InfinitePlace L) :
    algebraMap L (InfiniteAdeleRing L) l w = algebraMap L w.Completion l := rfl

variable {K L}

namespace InfinitePlaceData

variable (D : InfinitePlaceData K L)

section Derived

variable [NumberField K]


public theorem baseChangeRingEquiv_apply (z : (InfiniteAdeleRing K) ⊗[K] L) (w : InfinitePlace L) :
    D.baseChangeRingEquiv z w =
      D.placeEquiv (w.comap (algebraMap K L))
        (tensorPiAlgEquiv K L z (w.comap (algebraMap K L))) ⟨w, rfl⟩ := rfl


public theorem baseChangeRingEquiv_one_tmul (l : L) :
    D.baseChangeRingEquiv ((1 : InfiniteAdeleRing K) ⊗ₜ[K] l) =
      algebraMap L (InfiniteAdeleRing L) l := by
  funext w
  have h1 : D.baseChangeRingEquiv ((1 : InfiniteAdeleRing K) ⊗ₜ[K] l) w =
      D.placeEquiv (w.comap (algebraMap K L))
        ((1 : (w.comap (algebraMap K L)).Completion) ⊗ₜ[K] l) ⟨w, rfl⟩ := rfl
  rw [h1, algebraMap_infiniteAdeleRing_apply]
  exact D.placeEquiv_one_tmul (w.comap (algebraMap K L)) l ⟨w, rfl⟩


public theorem conorm_apply (x : InfiniteAdeleRing K) :
    D.conorm x = D.baseChangeRingEquiv (x ⊗ₜ[K] (1 : L)) := rfl


public theorem baseChangeRingEquiv_tmul_one (x : InfiniteAdeleRing K) :
    D.baseChangeRingEquiv (x ⊗ₜ[K] (1 : L)) = D.conorm x := rfl


public theorem conorm_algebraMap (c : K) :
    D.conorm (algebraMap K (InfiniteAdeleRing K) c) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L c) := by
  have key : (algebraMap K (InfiniteAdeleRing K) c) ⊗ₜ[K] (1 : L) =
      (1 : InfiniteAdeleRing K) ⊗ₜ[K] (algebraMap K L c) := by
    rw [Algebra.algebraMap_eq_smul_one (A := InfiniteAdeleRing K) c,
      Algebra.algebraMap_eq_smul_one (A := L) c, TensorProduct.smul_tmul]
  rw [conorm_apply, key, D.baseChangeRingEquiv_one_tmul]


public theorem baseChangeAlgEquiv_apply (z : (InfiniteAdeleRing K) ⊗[K] L) :
    D.baseChangeAlgEquiv z = D.baseChangeRingEquiv z := rfl


public theorem baseChangeAlgEquiv_one_tmul (l : L) :
    D.baseChangeAlgEquiv ((1 : InfiniteAdeleRing K) ⊗ₜ[K] l) =
      algebraMap L (InfiniteAdeleRing L) l :=
  D.baseChangeRingEquiv_one_tmul l

end Derived

end InfinitePlaceData

variable (K L)


variable {K L}


public theorem selfPlaceEquiv_apply_default (v : InfinitePlace K) (z : v.Completion ⊗[K] K) :
    selfPlaceEquiv K v z (default : v.Extension K) =
      Algebra.TensorProduct.rid K K v.Completion z := rfl


public theorem selfPlaceEquiv_one_tmul (v : InfinitePlace K) (l : K) (w : v.Extension K) :
    selfPlaceEquiv K v ((1 : v.Completion) ⊗ₜ[K] l) w = algebraMap K w.1.Completion l := by
  obtain rfl : w = default := Unique.eq_default w
  rw [selfPlaceEquiv_apply_default, Algebra.TensorProduct.rid_tmul]
  exact (Algebra.algebraMap_eq_smul_one l).symm


public theorem algebraMap_rat_injective :
    Function.Injective (algebraMap ℚ (InfiniteAdeleRing ℚ)) :=
  (algebraMap ℚ (InfiniteAdeleRing ℚ)).injective


public theorem gate_principal_two_ne_three :
    algebraMap ℚ (InfiniteAdeleRing ℚ) 2 ≠ algebraMap ℚ (InfiniteAdeleRing ℚ) 3 := fun h =>
  (by norm_num : (2 : ℚ) ≠ 3) (algebraMap_rat_injective h)


public theorem gate_baseChangeRingEquiv_separates :
    (selfInfinitePlaceData ℚ).baseChangeRingEquiv ((1 : InfiniteAdeleRing ℚ) ⊗ₜ[ℚ] (2 : ℚ))
      ≠ (selfInfinitePlaceData ℚ).baseChangeRingEquiv
          ((1 : InfiniteAdeleRing ℚ) ⊗ₜ[ℚ] (3 : ℚ)) := by
  rw [InfinitePlaceData.baseChangeRingEquiv_one_tmul,
    InfinitePlaceData.baseChangeRingEquiv_one_tmul]
  exact gate_principal_two_ne_three


public theorem gate_conorm_self_fixes_principal (q : ℚ) :
    (selfInfinitePlaceData ℚ).conorm (algebraMap ℚ (InfiniteAdeleRing ℚ) q)
      = algebraMap ℚ (InfiniteAdeleRing ℚ) q := by
  have h := (selfInfinitePlaceData ℚ).conorm_algebraMap q
  rwa [show algebraMap ℚ ℚ q = q from rfl] at h


public theorem gate_conorm_separates :
    (selfInfinitePlaceData ℚ).conorm (algebraMap ℚ (InfiniteAdeleRing ℚ) 2)
      ≠ (selfInfinitePlaceData ℚ).conorm (algebraMap ℚ (InfiniteAdeleRing ℚ) 3) := by
  rw [gate_conorm_self_fixes_principal, gate_conorm_self_fixes_principal]
  exact gate_principal_two_ne_three

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
