import Mathlib
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Lemma.AlgebraicGeometry.TwoAffineOpenCover
import Structure.AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option autoImplicit false

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry.SmoothProperCurve


namespace FiniteMapData

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : FiniteMapData c ε)

theorem range_subset_V : Set.range ε.1.base ⊆ (𝔉.V : Set C) := by
  rintro x ⟨y, rfl⟩
  have hx : ε.1.base y ∈ (⊤ : C.Opens) := trivial
  rw [← 𝔉.sup_eq_top, TopologicalSpace.Opens.mem_sup] at hx
  rcases hx with h | h
  · exact absurd ⟨y, rfl⟩ ((𝔉.mem_U_iff _).mp h)
  · exact h

theorem coe_U_eq_compl : (𝔉.U : Set C) = (Set.range ε.1.base)ᶜ :=
  Set.ext fun x => 𝔉.mem_U_iff x

theorem isAffineOpen_inf : IsAffineOpen (𝔉.U ⊓ 𝔉.V) := by
  rw [𝔉.inf_eq_basicOpen]; exact 𝔉.isAffineOpen_U.basicOpen _

theorem basicOpen_f_eq_basicOpen_g : C.basicOpen 𝔉.f = C.basicOpen 𝔉.g := by
  rw [← 𝔉.inf_eq_basicOpen, 𝔉.inf_eq_basicOpen_g]

def twoAffineOpenCover : C.TwoAffineOpenCover where
  U0 := 𝔉.V
  U1 := 𝔉.U
  isAffineOpen_U0 := 𝔉.isAffineOpen_V
  isAffineOpen_U1 := 𝔉.isAffineOpen_U
  sup_eq_top := by rw [sup_comm, 𝔉.sup_eq_top]
  isAffineOpen_inf := by rw [inf_comm]; exact 𝔉.isAffineOpen_inf

@[simp] theorem twoAffineOpenCover_U0 : 𝔉.twoAffineOpenCover.U0 = 𝔉.V := rfl
@[simp] theorem twoAffineOpenCover_U1 : 𝔉.twoAffineOpenCover.U1 = 𝔉.U := rfl

theorem range_subset_twoAffineOpenCover_U0 : Set.range ε.1.base ⊆ (𝔉.twoAffineOpenCover.U0 : Set C) :=
  𝔉.range_subset_V

theorem twoAffineOpenCover_U1_eq_compl : (𝔉.twoAffineOpenCover.U1 : Set C) = (Set.range ε.1.base)ᶜ :=
  𝔉.coe_U_eq_compl

theorem moduleFinite_U :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    letI : Algebra (Polynomial R) Γ(C, 𝔉.U) := (Polynomial.aeval 𝔉.f : Polynomial R →ₐ[R] Γ(C, 𝔉.U)).toRingHom.toAlgebra
    Module.Finite (Polynomial R) Γ(C, 𝔉.U) :=
  𝔉.finite_f

theorem moduleFinite_V :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.V
    letI : Algebra (Polynomial R) Γ(C, 𝔉.V) := (Polynomial.aeval 𝔉.g : Polynomial R →ₐ[R] Γ(C, 𝔉.V)).toRingHom.toAlgebra
    Module.Finite (Polynomial R) Γ(C, 𝔉.V) :=
  𝔉.finite_g

theorem levelSet_finite (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Module.Finite S (S ⊗[R] Γ(C, 𝔉.U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}) :=
  (𝔉.levelSet_free S s).1

theorem levelSet_finrank_eq (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Module.finrank S (S ⊗[R] Γ(C, 𝔉.U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}) = 𝔉.m :=
  (𝔉.levelSet_free S s).2.2

def LevelSetsGenericallyEtale : Prop :=
  ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s : S),
      IsUnit (Polynomial.aeval s D) →
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
      Algebra.Etale S (S ⊗[R] Γ(C, 𝔉.U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))})

end FiniteMapData

end AlgebraicGeometry.SmoothProperCurve

end
