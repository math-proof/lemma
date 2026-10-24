import Lemma.Definitions.Def_CohCarrier_Level
import Lemma.Definitions.Def_HeckeModule_IharaRungDatum
import Lemma.Definitions.Def_HeckeModule_IharaDataAt

set_option autoImplicit false

namespace IharaTower

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪]

structure CornerData (𝕋 : Type) [CommRing 𝕋] [Algebra 𝒪 𝕋]
    (V : Type) [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V] : Type where
  split : IdempotentSplitting 𝕋
  idx : Fin split.n
  pairing : LevelPairing (𝒪 := 𝒪) (split.CornerRing idx)
    ↥(cornerSubmodule (M := V) (split.e idx))

namespace CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]

abbrev cornerRing (cd : CornerData (𝒪 := 𝒪) 𝕋 V) : Type := cd.split.CornerRing cd.idx

abbrev cornerModule (cd : CornerData (𝒪 := 𝒪) 𝕋 V) : Type :=
  ↥(cornerSubmodule (M := V) (cd.split.e cd.idx))

end CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
variable {𝕋' : Type} [CommRing 𝕋'] [Algebra 𝒪 𝕋']
variable {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋' V']

structure DegeneracyDescent (cd : CornerData (𝒪 := 𝒪) 𝕋 V)
    (cd' : CornerData (𝒪 := 𝒪) 𝕋' V') (n : ℕ) : Type where
  iRaw : Fin n → V →ₗ[𝒪] V'
  jRaw : Fin n → V' →ₗ[𝒪] V
  corner_i : ∀ (k : Fin n) (v : V), v ∈ cornerSubmodule (M := V) (cd.split.e cd.idx) →
    iRaw k v ∈ cornerSubmodule (M := V') (cd'.split.e cd'.idx)
  corner_j : ∀ (k : Fin n) (v' : V'), v' ∈ cornerSubmodule (M := V') (cd'.split.e cd'.idx) →
    jRaw k v' ∈ cornerSubmodule (M := V) (cd.split.e cd.idx)

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

open CohCarrier in

abbrev H1CornerData (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type) [AddCommGroup A] [Module 𝒪 A]
    (𝕋 : Type) [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M H A)]
    [IsScalarTower 𝒪 𝕋 (H1 M H A)] : Type :=
  CornerData (𝒪 := 𝒪) 𝕋 (H1 M H A)

end IharaTower
