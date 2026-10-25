import Mathlib
import Instance.AlgebraicGeometry_ProjSpaceCechTwist
import Instance.AlgebraicGeometry_ProjSpaceCechGradedModule

set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech

section Carrier

variable (R : Type u) [CommRing R] (n : ℕ)

structure GradedModule where

  M : Type u
  [acg : AddCommGroup M]
  [modR : Module R M]

  grade : ℤ → Submodule R M

  xMul : Fin (n + 1) → M →ₗ[R] M

  xMul_mem_grade : ∀ (j : Fin (n + 1)) (d : ℤ), ∀ m ∈ grade d, xMul j m ∈ grade (d + 1)

  xMul_comm : ∀ (j k : Fin (n + 1)), xMul j ∘ₗ xMul k = xMul k ∘ₗ xMul j

attribute [instance] GradedModule.acg GradedModule.modR

variable {R n}
variable (D : GradedModule R n)


end Carrier

section GradSec

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n) (I : Finset (Fin (n + 1)))

structure GradedModule.Frac where

  denExp : Fin (n + 1) → ℕ

  hden : ∀ j ∉ I, denExp j = 0

  num : D.M

  hnum : num ∈ D.grade (∑ j, (denExp j : ℤ))


end GradSec

section GradAltC

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)


end GradAltC

section SecInclIrrel

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)


end SecInclIrrel

section Instances

variable (R : Type u) [CommRing R] (n : ℕ)

def GradedModule.freeGrade (d : ℤ) : Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  if 0 ≤ d then MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d.toNat else ⊥

theorem GradedModule.freeGrade_of_nonneg {d : ℤ} (hd : 0 ≤ d) :
    GradedModule.freeGrade R n d
      = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d.toNat := by
  simp [GradedModule.freeGrade, hd]

def GradedModule.freeXMul (j : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →ₗ[R] MvPolynomial (Fin (n + 1)) R where
  toFun p := X j * p
  map_add' p q := mul_add _ p q
  map_smul' r p := by simp only [RingHom.id_apply]; exact mul_smul_comm r (X j) p

def GradedModule.free : GradedModule R n where
  M := MvPolynomial (Fin (n + 1)) R
  grade := GradedModule.freeGrade R n
  xMul := GradedModule.freeXMul R n
  xMul_mem_grade j d m hm := by
    by_cases hd : 0 ≤ d
    · rw [GradedModule.freeGrade_of_nonneg R n hd] at hm
      rw [GradedModule.freeGrade_of_nonneg R n (by omega : (0:ℤ) ≤ d + 1)]
      have hdeg : (d + 1).toNat = 1 + d.toNat := by omega
      rw [hdeg, mem_homogeneousSubmodule]
      exact (isHomogeneous_X R j).mul hm
    · simp only [GradedModule.freeGrade, hd, if_false, Submodule.mem_bot] at hm
      simp [GradedModule.freeXMul, hm, Submodule.zero_mem]
  xMul_comm j k := by
    refine LinearMap.ext fun p => ?_
    show (X j : MvPolynomial (Fin (n + 1)) R) * (X k * p) = X k * (X j * p)
    ring

variable {R n}

def GradedModule.shift (D : GradedModule R n) (d₀ : ℤ) :
    GradedModule R n where
  M := D.M
  grade d := D.grade (d + d₀)
  xMul := D.xMul
  xMul_mem_grade j d m hm := by
    have h := D.xMul_mem_grade j (d + d₀) m hm
    convert h using 2; ring
  xMul_comm := D.xMul_comm

def GradedModule.pi {ι : Type} [Fintype ι] (D : ι → GradedModule R n) :
    GradedModule R n where
  M := ∀ k, (D k).M
  grade d := Submodule.pi Set.univ (fun k => (D k).grade d)
  xMul j := LinearMap.pi (fun k => (D k).xMul j ∘ₗ LinearMap.proj k)
  xMul_mem_grade j d m hm := by
    intro k _
    exact (D k).xMul_mem_grade j d (m k) (hm k (Set.mem_univ k))
  xMul_comm j k := by
    refine LinearMap.ext fun m => funext fun l => ?_
    exact LinearMap.congr_fun ((D l).xMul_comm j k) (m l)


end Instances

section FD

variable (R : Type u) [CommRing R] (n : ℕ)

abbrev GradedModule.FD (d₀ : ℤ) : GradedModule R n :=
  GradedModule.shift (GradedModule.free R n) d₀

variable {R n}


end FD

section SubMod

variable {R : Type u} [CommRing R] {n : ℕ}


end SubMod

section Hom

variable {R : Type u} [CommRing R] {n : ℕ}

structure GradedModule.Hom (D₁ D₂ : GradedModule R n) where

  toLinearMap : D₁.M →ₗ[R] D₂.M

  mem_grade : ∀ d m, m ∈ D₁.grade d → toLinearMap m ∈ D₂.grade d

  xMul_comm : ∀ j, toLinearMap ∘ₗ D₁.xMul j = D₂.xMul j ∘ₗ toLinearMap

variable {D₁ D₂ : GradedModule R n}


end Hom

section IsFG

variable {R : Type u} [CommRing R] {n : ℕ}

structure GradedModule.Presentation (D : GradedModule R n) where

  J : Type

  [fJ : Fintype J]

  d₀ : J → ℤ

  hom : GradedModule.Hom (GradedModule.pi (fun k => GradedModule.FD R n (d₀ k))) D

  surj : ∀ d, ∀ m ∈ D.grade d,
    ∃ m' ∈ (GradedModule.pi (fun k => GradedModule.FD R n (d₀ k))).grade d,
      hom.toLinearMap m' = m

attribute [instance] GradedModule.Presentation.fJ


end IsFG

section HomShift

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

def GradedModule.Hom.shift (φ : GradedModule.Hom D₁ D₂) (d₀ : ℤ) :
    GradedModule.Hom (GradedModule.shift D₁ d₀) (GradedModule.shift D₂ d₀) where
  toLinearMap := φ.toLinearMap
  mem_grade d m hm := φ.mem_grade (d + d₀) m hm
  xMul_comm j := φ.xMul_comm j


end HomShift

end ProjSpaceCech

end
