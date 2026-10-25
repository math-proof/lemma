/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/PerfectPairing/DualBasis.lean -/


import Def.LinearAlgebra.PerfectPairing.DualBasis
import Lemma.Matrix.PerfectPairing.DualBasis
open Module


namespace LinearMap.IsPerfPair

variable {A M N ι : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

variable [DecidableEq ι] [Finite ι]

variable (B : M →ₗ[A] N →ₗ[A] A) [B.IsPerfPair]

example (b : Basis ι A N) (i j : ι) :
    B (dualBasis B b i) (b j) = if j = i then 1 else 0 :=
  dualBasis_apply B b i j

example (b : Basis ι A N) (i : ι) : B (dualBasis B b i) (b i) = 1 := by
  simp

example (b : Basis ι A N) (i j : ι) (h : j ≠ i) :
    B (dualBasis B b i) (b j) = 0 := by
  simp [h]

example (b : Basis ι A N) (b' : Basis ι A M)
    (h : ∀ i j, B (b' i) (b j) = if j = i then 1 else 0) :
    b' = dualBasis B b :=
  eq_dualBasis_of B b b' h

example (b : Basis ι A N) (b₁ b₂ : Basis ι A M)
    (h₁ : ∀ i j, B (b₁ i) (b j) = if j = i then 1 else 0)
    (h₂ : ∀ i j, B (b₂ i) (b j) = if j = i then 1 else 0) :
    b₁ = b₂ :=
  (eq_dualBasis_of B b b₁ h₁).trans (eq_dualBasis_of B b b₂ h₂).symm

example (b : Basis ι A N) :
    ∃ b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
  exists_dualBasis B b

example (b : Basis ι A N) :
    ∃! b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
  existsUnique_dualBasis B b

example (b : Basis (Fin 1) A N) (i : Fin 1) :
    B (dualBasis B b i) (b i) = 1 := by
  simp

example (b : Basis Empty A N) :
    ∃! b' : Basis Empty A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
  existsUnique_dualBasis B b

/-- Concrete pairing between distinct types: `M` is the dual of `N`. -/
example (i j : Fin 2) :
    (LinearMap.id : Module.Dual ℚ (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ)
        (dualBasis
          (LinearMap.id :
            Module.Dual ℚ (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ)
          (Pi.basisFun ℚ (Fin 2)) i) ((Pi.basisFun ℚ (Fin 2)) j) =
      if j = i then 1 else 0 :=
  dualBasis_apply
    (LinearMap.id :
      Module.Dual ℚ (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ) _ i j

example :
    ∃! b' : Basis (Fin 2) ℚ (Module.Dual ℚ (Fin 2 → ℚ)), ∀ i j,
      (LinearMap.id : Module.Dual ℚ (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ)
        (b' i) ((Pi.basisFun ℚ (Fin 2)) j) = if j = i then 1 else 0 :=
  existsUnique_dualBasis
    (LinearMap.id : Module.Dual ℚ (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] ℚ) _

end LinearMap.IsPerfPair
