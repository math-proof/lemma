import Mathlib
import Structure.NeronModelInfra_WeakNeronModel
import Def.AlgebraicGeometry_KaehlerModule
import Def.NeronModelInfra_TopFormOrder
import Lemma.NeronModelInfra.SmoothnessDefect

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace NeronModelInfra

section StalkAlgebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (y : Y)


end StalkAlgebra

section Reading

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ(gK.topDifferentials d, ⊤))

structure ComponentReading where

  Y : Scheme.{u}

  f : Y ⟶ Spec (CommRingCat.of R)

  smooth : Smooth f

  locallyOfFiniteType : LocallyOfFiniteType f

  e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK

  isOpenImmersion : IsOpenImmersion e.1

  y : Y

  hy : f.base y = IsLocalRing.closedPoint R

  hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y

  isDomain : IsDomain (Y.presheaf.stalk y)

  isDiscreteValuationRing : IsDiscreteValuationRing (Y.presheaf.stalk y)

  algebra : Algebra R (Y.presheaf.stalk y)

  halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))

  algebraK : Algebra K (FractionRing (Y.presheaf.stalk y))

  isScalarTower : IsScalarTower R K (FractionRing (Y.presheaf.stalk y))

  b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])

  U : XK.Opens

  hU : IsAffineOpen U

  algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y))

  isScalarTowerU : letI := gK.sectionsAlgebra U
    IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y))

  hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
    (schemeHomOverComp
      (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
        (⟨Y.fromSpecStalk y, halg⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
      e).1

  ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U))

  hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω

  a : FractionRing (Y.presheaf.stalk y)

  ha : letI := gK.sectionsAlgebra U
    TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
      a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
        (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)

  ha0 : a ≠ 0

attribute [instance] ComponentReading.smooth ComponentReading.locallyOfFiniteType
  ComponentReading.isOpenImmersion ComponentReading.isDomain ComponentReading.isDiscreteValuationRing

variable {R K gK d ω}


end Reading

section Minimal

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ(gK.topDifferentials d, ⊤))

structure MinimalComponentData where

  ι : Type u

  finite : Finite ι

  nonempty : Nonempty ι

  C : ι → ComponentReading R K gK d ω

  isSeparated : ∀ c, IsSeparated (C c).f

  quasiCompact : ∀ c, QuasiCompact (C c).f

  isIso : ∀ c, IsIso (C c).e.1

  hgen : ∀ c (y' : ↥(C c).Y), (C c).f.base y' = IsLocalRing.closedPoint R → (C c).y ⤳ y'

  inequiv : ∀ c c', c ≠ c' → ∀ (U : ((C c).Y).Opens), (C c).y ∈ U →
    ∀ u : SchemeHomOver (U.ι ≫ (C c).f) (C c').f,
      (genericFibreRestrict R K (C c').f (U.ι ≫ (C c).f) u).1 ≫ (C c').e.1 ≠
        (genericFibreRestrict R K (C c).f (U.ι ≫ (C c).f) ⟨U.ι, rfl⟩).1 ≫ (C c).e.1

attribute [instance] MinimalComponentData.finite MinimalComponentData.nonempty

variable {R K gK d ω}


end Minimal

section Gates

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ} {ω : Γ(gK.topDifferentials d, ⊤)}


end Gates

end NeronModelInfra

end

/--
info: 'NeronModelInfra.fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra

/--
info: 'NeronModelInfra.ComponentReading.n_eq_one_of_a_eq_uniformizer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.ComponentReading.n_eq_one_of_a_eq_uniformizer

/--
info: 'NeronModelInfra.MinimalComponentData.IsOmegaMinimal.n_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.MinimalComponentData.IsOmegaMinimal.n_eq
