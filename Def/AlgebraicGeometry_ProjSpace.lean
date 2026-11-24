module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Instance.AlgebraicGeometry_ProjSpace
public import Structure.AlgebraicGeometry_ProjSpace
public import Notation.AlgebraicGeometry_ProjSpace
set_option autoImplicit false
set_option linter.unusedVariables false


public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section PnSetup

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace

def grad0Equiv : R ≃+* (𝒜 0) where
  toFun r := ⟨C r, (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_C _ r)⟩
  invFun p := MvPolynomial.constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    ext : 1
    have hp : p.1.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 _).mp p.2
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [MvPolynomial.constantCoeff]
    · rw [MvPolynomial.coeff_C, if_neg (Ne.symm hd)]
      by_contra h
      refine hd (Finsupp.ext fun i => ?_)

      have hdeg : (Finsupp.weight (1 : Fin (n + 1) → ℕ)) d = 0 := hp (fun h0 => h h0.symm)
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Finsupp.sum] at hdeg
      by_cases hi : i ∈ d.support
      · exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hdeg i hi
      · exact Finsupp.notMem_support_iff.mp hi
  map_mul' a b := by ext : 1; simp
  map_add' a b := by ext : 1; simp

def π : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (grad0Equiv R n).toRingHom)

end PnSetup

section StdCover

open MvPolynomial AlgebraicGeometry.Proj

variable (R : Type u) [CommRing R] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

open scoped AlgebraicGeometry_ProjSpace

end StdCover

section Setup

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace

def ratio (i k : Fin (n + 1)) : Away 𝒜 (MvPolynomial.X i) :=
  Away.mk 𝒜 (X_mem_one R n i) 1 (MvPolynomial.X k)
    (by simpa using X_mem_one R n k)

end Setup

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace

def affineOpenCover : (Proj 𝒜).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 (fun j => MvPolynomial.X j)
    (fun j => X_mem_one R n j) (fun _ => one_pos)
    (irrelevant_le_span_X R n)

end StdCover


section ProdOver

variable (R : Type u) [CommRing R]


def prodPr :
    ∀ {m : ℕ} (e : Fin m → ℕ) (k : Fin m),
      prodOver R e ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R)
  | m + 1, e, ⟨0, _⟩ => pullback.fst _ _
  | m + 1, e, ⟨k + 1, hk⟩ =>
    pullback.snd _ _ ≫ prodPr (e ∘ Fin.succ) ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

def prodLiftAux {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) :
    ∀ {m : ℕ} (e : Fin m → ℕ)
      (g : ∀ k, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R))
      (_ : ∀ k, g k ≫ π R (e k) = s),
      Σ' (l : X ⟶ prodOver R e), l ≫ prodOverπ R e = s
  | 0, _, _, _ => ⟨s, Category.comp_id s⟩
  | m + 1, e, g, hg =>
    let prev := @prodLiftAux X s m (e ∘ Fin.succ)
      (fun k => g k.succ) (fun k => hg k.succ)
    ⟨pullback.lift (g 0) prev.1 (by rw [hg 0, prev.2]),
     by
      show pullback.lift (g 0) prev.1 _ ≫ pullback.fst _ _ ≫ π R (e 0) = s
      rw [← Category.assoc, pullback.lift_fst]; exact hg 0⟩

def prodLift {X : Scheme.{u}} (s : X ⟶ Spec (.of R)) {m : ℕ} (e : Fin m → ℕ)
    (g : ∀ k, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R))
    (hg : ∀ k, g k ≫ π R (e k) = s) :
    X ⟶ prodOver R e :=
  (prodLiftAux R s e g hg).1

end ProdOver

section MapGraded

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace

def mvMapGraded : 𝒜R →+*ᵍ 𝒜A where
  toRingHom := MvPolynomial.map (algebraMap R A)
  map_mem hx := (mem_homogeneousSubmodule _ _).mpr (((mem_homogeneousSubmodule _ _).mp hx).map _)

def map : Proj 𝒜A ⟶ Proj 𝒜R :=
  Proj.map (mvMapGraded R A n) (irrelevant_le_map_mvMapGraded R A n)

end MapGraded

end ProjSpace


end AlgebraicGeometry

end
