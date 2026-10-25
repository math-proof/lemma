import Def.CohCarrier_Level
import Def.HeckeModule_IharaRungDatum
import Lemma.HeckeModule.IharaDataAt
import Structure.CohCarrier_LevelPairing
import Abbrev.CohCarrier_LevelPairing

set_option autoImplicit false

namespace IharaTower

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪]


namespace CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]

end CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
variable {𝕋' : Type} [CommRing 𝕋'] [Algebra 𝒪 𝕋']
variable {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋' V']


namespace DegeneracyDescent

variable {cd : CornerData (𝒪 := 𝒪) 𝕋 V} {cd' : CornerData (𝒪 := 𝒪) 𝕋' V'} {n : ℕ}

noncomputable def iLeg (D : DegeneracyDescent cd cd' n) (k : Fin n) :
    cd.cornerModule →ₗ[𝒪] cd'.cornerModule where
  toFun v := ⟨D.iRaw k v, D.corner_i k v v.2⟩
  map_add' := by intro a b; apply Subtype.ext; simp
  map_smul' := by intro r a; apply Subtype.ext; simp

noncomputable def jLeg (D : DegeneracyDescent cd cd' n) (k : Fin n) :
    cd'.cornerModule →ₗ[𝒪] cd.cornerModule where
  toFun v' := ⟨D.jRaw k v', D.corner_j k v' v'.2⟩
  map_add' := by intro a b; apply Subtype.ext; simp
  map_smul' := by intro r a; apply Subtype.ext; simp

@[simp] theorem iLeg_apply (D : DegeneracyDescent cd cd' n) (k : Fin n)
    (v : cd.cornerModule) : (↑(D.iLeg k v) : V') = D.iRaw k ↑v := rfl

@[simp] theorem jLeg_apply (D : DegeneracyDescent cd cd' n) (k : Fin n)
    (v' : cd'.cornerModule) : (↑(D.jLeg k v') : V) = D.jRaw k ↑v' := rfl

noncomputable def toLegDatum (D : DegeneracyDescent cd cd' n)
    (table : Fin n → Fin n → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin n) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin n) (m : cd.cornerModule),
      D.jLeg k (D.iLeg k' m) = table k k' • m) :
    RungAssembly.LegDatum (𝒪 := 𝒪) cd.pairing cd'.pairing n :=
  ⟨D.iLeg, D.jLeg, adjoint_leg, table, htable⟩

theorem toLegDatum_iLeg (D : DegeneracyDescent cd cd' n) (table : Fin n → Fin n → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin n) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin n) (m : cd.cornerModule),
      D.jLeg k (D.iLeg k' m) = table k k' • m) :
    (D.toLegDatum table adjoint_leg htable).iLeg = D.iLeg := rfl

theorem toLegDatum_jLeg (D : DegeneracyDescent cd cd' n) (table : Fin n → Fin n → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin n) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin n) (m : cd.cornerModule),
      D.jLeg k (D.iLeg k' m) = table k k' • m) :
    (D.toLegDatum table adjoint_leg htable).jLeg = D.jLeg := rfl

theorem toLegDatum_table (D : DegeneracyDescent cd cd' n) (table : Fin n → Fin n → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin n) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin n) (m : cd.cornerModule),
      D.jLeg k (D.iLeg k' m) = table k k' • m) :
    (D.toLegDatum table adjoint_leg htable).table = table := rfl

end DegeneracyDescent

end IharaTower
