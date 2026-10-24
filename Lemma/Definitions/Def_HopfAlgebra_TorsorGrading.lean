import Mathlib

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace HopfAlgebra.TorsorGrading

open TensorProduct

section Grading

variable (Λ : Type) [AddCommGroup Λ] [DecidableEq Λ]
variable {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H]
variable (π : H →ₐc[R] MonoidAlgebra R (Multiplicative Λ))

def gradingCoaction : H →ₗ[R] MonoidAlgebra R (Multiplicative Λ) ⊗[R] H :=
  (LinearMap.rTensor H π.toLinearMap) ∘ₗ Coalgebra.comul

def gradingComponents : H →ₗ[R] (Multiplicative Λ →₀ H) :=
  (TensorProduct.finsuppScalarLeft R H (Multiplicative Λ)).toLinearMap ∘ₗ
    ((MonoidAlgebra.coeffLinearEquiv R).rTensor H).toLinearMap ∘ₗ gradingCoaction Λ π

def componentProj (j : Λ) : H →ₗ[R] H :=
  (Finsupp.lapply (Multiplicative.ofAdd j)) ∘ₗ gradingComponents Λ π

def gradedPiece (j : Λ) : Submodule R H where
  carrier := {t : H | gradingComponents Λ π t = Finsupp.single (Multiplicative.ofAdd j) t}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb, ← Finsupp.single_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, Finsupp.single_zero]
  smul_mem' := fun c a ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_smul, ha, Finsupp.smul_single]

omit [DecidableEq Λ] in
theorem gradingCoaction_apply (t : H) :
    gradingCoaction Λ π t = (LinearMap.rTensor H π.toLinearMap) ((Coalgebra.comul (R := R)) t) := rfl

theorem gradingComponents_apply (t : H) :
    gradingComponents Λ π t =
      (TensorProduct.finsuppScalarLeft R H (Multiplicative Λ))
        (((MonoidAlgebra.coeffLinearEquiv R).rTensor H) (gradingCoaction Λ π t)) := rfl

theorem componentProj_apply (j : Λ) (t : H) :
    componentProj Λ π j t = gradingComponents Λ π t (Multiplicative.ofAdd j) := rfl

theorem mem_gradedPiece_iff (j : Λ) (t : H) :
    t ∈ gradedPiece Λ π j ↔ gradingComponents Λ π t = Finsupp.single (Multiplicative.ofAdd j) t := Iff.rfl

def blockComponents : H →ₗ[R] (Multiplicative Λ →₀ H) :=
  (TensorProduct.finsuppScalarLeft R H (Multiplicative Λ)).toLinearMap ∘ₗ
    ((MonoidAlgebra.coeffLinearEquiv R).rTensor H).toLinearMap ∘ₗ
    (LinearMap.rTensor H π.toLinearMap) ∘ₗ Coalgebra.comul

def blockPiece (ε : H) (j : Λ) : Submodule R H where
  carrier := {t : H | blockComponents Λ π t = Finsupp.single (Multiplicative.ofAdd j) t ∧ t * ε = t}
  add_mem' := fun {x y} hx hy => by
    obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
    refine ⟨?_, by rw [add_mul, hx2, hy2]⟩
    rw [map_add, hx1, hy1, ← Finsupp.single_add]
  zero_mem' := by
    refine ⟨?_, by rw [zero_mul]⟩
    rw [map_zero, Finsupp.single_zero]
  smul_mem' := fun c x hx => by
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨?_, by rw [smul_mul_assoc, hx2]⟩
    rw [map_smul, hx1, Finsupp.smul_single]

theorem blockComponents_eq : blockComponents Λ π = gradingComponents Λ π := rfl

theorem mem_blockPiece_iff (ε : H) (j : Λ) (t : H) :
    t ∈ blockPiece Λ π ε j ↔ t ∈ gradedPiece Λ π j ∧ t * ε = t := Iff.rfl

end Grading

end HopfAlgebra.TorsorGrading

end
