import Def.HeckeModule_IharaRungDatum
import Instance.IharaLemma_IdempotentSplitting
import Def.HeckeModule_IharaDataAt
import Structure.HeckeModule_IharaDataAt

namespace IharaTower

variable {𝒪 : Type} [CommRing 𝒪]
  {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}


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


theorem cornerRung_res : (cornerRung S S' i₀ i₀' P P' L c res).res = res := rfl

theorem cornerRung_i :
    (cornerRung S S' i₀ i₀' P P' L c res).i = RungAssembly.iComb L c := rfl

theorem cornerRung_j :
    (cornerRung S S' i₀ i₀' P P' L c res).j = RungAssembly.jComb L c := rfl

theorem cornerRung_delta :
    (cornerRung S S' i₀ i₀' P P' L c res).Δ = RungAssembly.deltaComb L c := rfl

end CornerRung

end IharaTower
