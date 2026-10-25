import Mathlib
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Structure.AlgebraicGeometry_TwoAffineOpenCover

set_option autoImplicit false

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry.SmoothProperCurve

structure FiniteMapData {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) where

  U : C.Opens

  V : C.Opens

  f : Γ(C, U)

  g : Γ(C, V)

  m : ℕ
  isAffineOpen_U : IsAffineOpen U
  isAffineOpen_V : IsAffineOpen V
  sup_eq_top : U ⊔ V = ⊤

  mem_U_iff : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base

  inf_eq_basicOpen : U ⊓ V = C.basicOpen f

  inf_eq_basicOpen_g : U ⊓ V = C.basicOpen g

  res_f_mul_res_g : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1

  finite_f : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite

  finite_g : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite

  levelSet_free : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m

namespace FiniteMapData

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : FiniteMapData c ε)


end FiniteMapData

end AlgebraicGeometry.SmoothProperCurve

end
