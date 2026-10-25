-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ProjTwistDatum.lean: instance decls only.
import Mathlib
import Lemma.AlgebraicGeometry.ProjSpaceCover
import Instance.AlgebraicGeometry_ProjSpaceCechGradedModule
import Lemma.AlgebraicGeometry.ProjTwistDatum

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization


namespace AlgebraicGeometry
namespace ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

instance twistObj.addCommGroup (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : AddCommGroup (twistObj π φ m U) :=
  (twistObj.equivSections π φ m U).addCommGroup

instance twistObj.moduleSections (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Module Γ(X, U) (twistObj π φ m U) where
  smul a g := ⟨fun i => restrictFun inf_le_left a * g.val i, smul_mem_twistSections φ a g.compat⟩
  one_smul g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ 1 * g.val i = g.val i
    rw [map_one, one_mul]
  mul_smul a b g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (a * b) * g.val i = restrictFun _ a * (restrictFun _ b * g.val i)
    rw [map_mul, mul_assoc]
  smul_zero a := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ a * (0 : Γ(X, U ⊓ pullbackChart φ i)) = 0
    rw [mul_zero]
  smul_add a g g' := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ a * (g.val i + g'.val i) = restrictFun _ a * g.val i + restrictFun _ a * g'.val i
    rw [mul_add]
  add_smul a b g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (a + b) * g.val i = restrictFun _ a * g.val i + restrictFun _ b * g.val i
    rw [map_add, add_mul]
  zero_smul g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ 0 * g.val i = 0
    rw [map_zero, zero_mul]

instance twistObj.module (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Module A (twistObj π φ m U) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  Module.compHom (twistObj π φ m U) (algebraMap A (Γ(X, U) : Type u))

end ProjSpace
end AlgebraicGeometry


namespace AlgebraicGeometry.ProjSpace


variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

section GradedModuleOfTwist

variable (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

instance twistFam.addCommGroup (π : X ⟶ Spec (.of A)) : AddCommGroup (twistFam π φ) := inferInstanceAs (AddCommGroup (ℤ → ∀ i : Fin (N + 1), Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)))

instance twistFam.module (π : X ⟶ Spec (.of A)) : Module A (twistFam π φ) := by
  letI : ∀ i : Fin (N + 1), Module A (Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i) : Type u) := fun i => moduleOfHom π _
  exact inferInstanceAs (Module A (ℤ → ∀ i : Fin (N + 1), Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)))

end GradedModuleOfTwist

end AlgebraicGeometry.ProjSpace


end
