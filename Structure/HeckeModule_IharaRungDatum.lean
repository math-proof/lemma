import Mathlib.Algebra.Module.Torsion.Basic

set_option autoImplicit false

namespace IharaTower

variable {𝒪 : Type} [CommRing 𝒪]

structure LevelPairing (T : Type) [CommRing T] [Algebra 𝒪 T]
    (M : Type) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M] where
  B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪
  selfAdjoint : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n)
  perfect : Function.Bijective B

structure RungDatum (T : Type) [CommRing T] [Algebra 𝒪 T]
    (T' : Type) [CommRing T'] [Algebra 𝒪 T']
    (M : Type) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    (M' : Type) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    (P : LevelPairing (𝒪 := 𝒪) T M) (P' : LevelPairing (𝒪 := 𝒪) T' M') where
  res : T' →ₐ[𝒪] T
  i : M →ₗ[𝒪] M'
  j : M' →ₗ[𝒪] M
  Δ : T
  adjoint : ∀ (m' : M') (m : M), P.B (j m') m = P'.B m' (i m)
  comp_eq_smul : ∀ m : M, j (i m) = Δ • m

section Clauses

variable {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}


end Clauses

namespace RungAssembly

variable {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}


variable (P P') in

structure LegDatum (n : ℕ) where
  iLeg : Fin n → (M →ₗ[𝒪] M')
  jLeg : Fin n → (M' →ₗ[𝒪] M)
  adjoint_leg : ∀ (k : Fin n) (m' : M') (m : M), P.B (jLeg k m') m = P'.B m' (iLeg k m)
  table : Fin n → Fin n → T
  htable : ∀ (k k' : Fin n) (m : M), jLeg k (iLeg k' m) = table k k' • m

variable {n : ℕ}


end RungAssembly

end IharaTower
