import Mathlib
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

structure IsIndexOneExtension (R R' : Type u) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    [Algebra R R'] [IsLocalHom (algebraMap R R')] : Prop where

  map_maximalIdeal :
    Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R'

  formallySmooth_residueField :
    Algebra.FormallySmooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')


section PointGenericFibre

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {K' : Type u} [CommRing K'] [Algebra R' K'] [Algebra R K'] [IsScalarTower R R' K']
  [Algebra K K'] [IsScalarTower R K K']


variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}


end PointGenericFibre

structure ModelFamily (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K)) where

  ι : Type u

  X : ι → Scheme.{u}

  str : ∀ i, X i ⟶ Spec (CommRingCat.of R)

  chart : ∀ i, SchemeHomOver (pullback.snd (str i) (specGenericFibreInclusion R K)) gK

  isOpenImmersion_chart : ∀ i, IsOpenImmersion (chart i).1

attribute [instance] ModelFamily.isOpenImmersion_chart


section Gates

variable (R K : Type u) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]


end Gates

end NeronModelInfra

end

/--
info: 'NeronModelInfra.IsIndexOneExtension.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.IsIndexOneExtension.refl

/--
info: 'NeronModelInfra.gate_catchesIndexOnePoints_trivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_catchesIndexOnePoints_trivial

/--
info: 'NeronModelInfra.gate_not_catchesIndexOnePoints_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NeronModelInfra.gate_not_catchesIndexOnePoints_empty
