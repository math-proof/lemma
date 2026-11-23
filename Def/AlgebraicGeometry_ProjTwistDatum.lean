import Mathlib
import Def.AlgebraicGeometry_ProjSpaceCover
import Def.AlgebraicGeometry_ProjSpaceCechGradedModule
import Instance.AlgebraicGeometry_ProjTwistDatum
import Structure.AlgebraicGeometry_ProjTwistDatum
import Notation.AlgebraicGeometry_ProjTwistDatum

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization

namespace MvPolynomial.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (N : ℕ)

open scoped AlgebraicGeometry_ProjTwistDatum

end MvPolynomial.ProjSpace

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


def twistSections (m : ℕ) (U : X.Opens) : AddSubgroup (∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)) where
  carrier := {g | TwistCompat φ m U g}
  zero_mem' := fun i j => by simp
  add_mem' := by
    intro g g' hg hg' i j
    simp only [Pi.add_apply, map_add, hg i j, hg' i j, mul_add]
  neg_mem' := by
    intro g hg i j
    simp only [Pi.neg_apply, map_neg, hg i j, mul_neg]

end ProjSpace

end AlgebraicGeometry

namespace AlgebraicGeometry
namespace ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

def twistObj.equivSections (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) :
    twistObj π φ m U ≃ twistSections φ m U where
  toFun g := ⟨g.val, g.compat⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def twistRes (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) {U U' : X.Opens} (h : U ≤ U') : twistObj π φ m U' →ₗ[A] twistObj π φ m U :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U'
  { toFun := fun g => ⟨fun i => restrictFun (inf_le_inf_right (pullbackChart φ i) h) (g.val i),
      res_mem_twistSections φ h g.compat⟩
    map_add' := fun g g' => by
      refine twistObj.ext (_root_.funext fun i => ?_)
      show restrictFun _ (g.val i + g'.val i) = restrictFun _ (g.val i) + restrictFun _ (g'.val i)
      rw [map_add]
    map_smul' := fun r g => by
      refine twistObj.ext (_root_.funext fun i => ?_)
      show restrictFun _ (restrictFun _ (algebraMap A (Γ(X, U') : Type u) r) * g.val i)
        = restrictFun _ (algebraMap A (Γ(X, U) : Type u) r) * restrictFun _ (g.val i)
      rw [map_mul, restrictFun_restrictFun, ← restrictFun_algebraMap π h r, restrictFun_restrictFun] }

def twist (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) : OModulePresheaf π where
  obj U := twistObj π φ m U
  addCommGroup _ := inferInstance
  moduleSections U := twistObj.moduleSections π φ m U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun r a g => by
      show (r • a) • g = algebraMap A (Γ(X, U) : Type u) r • (a • g)
      rw [Algebra.smul_def, mul_smul]⟩
  res h := twistRes π φ m h
  res_smul h a g := by
    change twistRes π φ m h (a • g) = restrictFun h a • twistRes π φ m h g
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (restrictFun _ a * g.val i) = restrictFun _ (restrictFun _ a) * restrictFun _ (g.val i)
    rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun]
  res_refl U := by
    refine LinearMap.ext fun g => twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (g.val i) = g.val i
    exact restrictFun_refl _
  res_comp h h' := by
    refine LinearMap.ext fun g => twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (g.val i) = restrictFun _ (restrictFun _ (g.val i))
    rw [restrictFun_restrictFun]

end ProjSpace
end AlgebraicGeometry

namespace MvPolynomial.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

def pullbackOverlap (i i' : Fin (N + 1)) : X.Opens :=
  φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i * MvPolynomial.X i')

end MvPolynomial.ProjSpace

namespace MvPolynomial.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

end MvPolynomial.ProjSpace

namespace MvPolynomial.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}

section GradedModuleOfTwist

variable (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

def twistFam (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) : Type u := ℤ → ∀ i : Fin (N + 1), Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)

@[reducible] def moduleOfHom (π : X ⟶ Spec (.of A)) (W : X.Opens) : Module A (Γ(X, W) : Type u) :=
  (Scheme.TwoAffineOpenCover.algebraOfHom π W).toModule

def twistGrade (π : X ⟶ Spec (.of A)) (d : ℤ) : Submodule A (twistFam π φ) where
  carrier := {f | (∀ d', d' ≠ d → f d' = 0) ∧ (d < 0 → f d = 0) ∧ (0 ≤ d → TwistCompat φ d.toNat ⊤ (f d))}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => rfl, fun _ => (twistSections φ d.toNat ⊤).zero_mem⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨fun d' hd' => ?_, fun hd => ?_, fun hd => (twistSections φ d.toNat ⊤).add_mem (hf3 hd) (hg3 hd)⟩
    · show f d' + g d' = 0
      rw [hf1 d' hd', hg1 d' hd', add_zero]
    · show f d + g d = 0
      rw [hf2 hd, hg2 hd, add_zero]
  smul_mem' := by
    rintro r f ⟨hf1, hf2, hf3⟩
    refine ⟨fun d' hd' => ?_, fun hd => ?_, fun hd => ?_⟩
    · funext i
      show _ * f d' i = 0
      rw [hf1 d' hd']
      exact mul_zero _
    · funext i
      show _ * f d i = 0
      rw [hf2 hd]
      exact mul_zero _
    · intro i j
      have hc := hf3 hd i j
      have hi := restrictFun_algebraMap' π
        (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i) r
      have hj := restrictFun_algebraMap' π
        (le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
          ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ (⊤ : X.Opens) ⊓ pullbackChart φ j) r
      show restrictFun _ ((Scheme.TwoAffineOpenCover.algebraOfHom π _).algebraMap r * f d i)
        = _ * restrictFun _ ((Scheme.TwoAffineOpenCover.algebraOfHom π _).algebraMap r * f d j)
      rw [map_mul, map_mul, hc, hi, hj]
      ring

def twistXMul (π : X ⟶ Spec (.of A)) (j : Fin (N + 1)) : twistFam π φ →ₗ[A] twistFam π φ where
  toFun f := fun d i => restrictFun inf_le_right (frameUnit φ i j) * f (d - 1) i
  map_add' f g := by
    funext d i
    show restrictFun _ (frameUnit φ i j) * (f (d - 1) i + g (d - 1) i) = _ * _ + _ * _
    rw [mul_add]
  map_smul' r f := by
    funext d i
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π ((⊤ : X.Opens) ⊓ pullbackChart φ i)
    show restrictFun _ (frameUnit φ i j) * (algebraMap A (Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i) : Type u) r * f (d - 1) i)
      = algebraMap A (Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i) : Type u) r * (restrictFun _ (frameUnit φ i j) * f (d - 1) i)
    ring

end GradedModuleOfTwist

end MvPolynomial.ProjSpace

namespace MvPolynomial.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

def twistGradedModule (π : X ⟶ Spec (.of A)) : ProjSpaceCech.GradedModule A N where
  M := twistFam π φ
  grade := twistGrade φ π
  xMul := twistXMul φ π
  xMul_mem_grade j d f hf := twistXMul_mem φ π j d f hf
  xMul_comm j k := twistXMul_comm φ π j k

def twistGradeToObj (π : X ⟶ Spec (.of A)) {d : ℤ} (hd : 0 ≤ d) (f : twistFam π φ) (hf : f ∈ twistGrade φ π d) : twistObj π φ d.toNat ⊤ :=
  ⟨f d, hf.2.2 hd⟩

def objToTwistFam (π : X ⟶ Spec (.of A)) (m : ℕ) (g : twistObj π φ m ⊤) : twistFam π φ := fun d => if d = m then g.val else 0

end MvPolynomial.ProjSpace

namespace MvPolynomial.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

end MvPolynomial.ProjSpace

namespace MvPolynomial.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

def twistGradeEquiv (π : X ⟶ Spec (.of A)) {d : ℤ} (hd : 0 ≤ d) :
    twistGrade φ π d ≃ₗ[A] twistObj π φ d.toNat ⊤ where
  toFun f := twistGradeToObj φ π hd f.1 f.2
  invFun g := ⟨objToTwistFam φ π d.toNat g, by
    have h := objToTwistFam_mem φ π d.toNat g
    rwa [Int.toNat_of_nonneg hd] at h⟩
  map_add' f g := rfl
  map_smul' r f := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show (Scheme.TwoAffineOpenCover.algebraOfHom π ((⊤ : X.Opens) ⊓ pullbackChart φ i)).algebraMap r * f.1 d i
      = restrictFun inf_le_left ((Scheme.TwoAffineOpenCover.algebraOfHom π (⊤ : X.Opens)).algebraMap r) * f.1 d i
    rw [restrictFun_algebraMap' π]
  left_inv f := by
    apply Subtype.ext
    funext d'
    show (if d' = ((d.toNat : ℕ) : ℤ) then f.1 d else 0) = f.1 d'
    rw [Int.toNat_of_nonneg hd]
    split_ifs with h
    · rw [h]
    · exact (f.2.1 d' h).symm
  right_inv g := by
    refine twistObj.ext ?_
    show (if d = ((d.toNat : ℕ) : ℤ) then g.val else 0) = g.val
    rw [Int.toNat_of_nonneg hd, if_pos rfl]

end MvPolynomial.ProjSpace

end
