import Structure.HeckeModule_IharaRungDatum
import Instance.IharaLemma_IdempotentSplitting
import Def.HeckeModule_IharaDataAt

namespace IharaTower

variable {𝒪 : Type} [CommRing 𝒪]
  {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}

structure IsIharaDataAt (D : RungDatum T T' M M' P P')
    (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪) : Prop where
  cotorsion_comap_eq :
    Submodule.comap D.j (((RingHom.ker πT) • (⊤ : Submodule T M)).restrictScalars 𝒪) =
      ((RingHom.ker πT') • (⊤ : Submodule T' M')).restrictScalars 𝒪

section CornerRung

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪]
  {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup V'] [Module 𝒪 V']
  {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
  [Module 𝕋 V] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋 V] [IsScalarTower 𝒪 𝕋' V']
  (S : IdempotentSplitting 𝕋) (S' : IdempotentSplitting 𝕋') (i₀ : Fin S.n) (i₀' : Fin S'.n)
  (P : LevelPairing (𝒪 := 𝒪) (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀)))
  (P' : LevelPairing (𝒪 := 𝒪) (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀')))
  {n : ℕ}
  (L : RungAssembly.LegDatum (T := S.CornerRing i₀) (T' := S'.CornerRing i₀')
    (M := ↥(cornerSubmodule (M := V) (S.e i₀)))
    (M' := ↥(cornerSubmodule (M := V') (S'.e i₀')))
    (𝒪 := 𝒪) P P' n)
  (c : Fin n → S.CornerRing i₀) (res : S'.CornerRing i₀' →ₐ[𝒪] S.CornerRing i₀)


end CornerRung

end IharaTower
