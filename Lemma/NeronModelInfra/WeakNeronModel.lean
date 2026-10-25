import Mathlib
import Lemma.AlgebraicGeometry.NeronModelEndomorphismExtension
import Structure.NeronModelInfra_WeakNeronModel

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra


theorem IsIndexOneExtension.refl (R : Type u) [CommRing R] [IsLocalRing R] :
    IsIndexOneExtension R R where
  map_maximalIdeal := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  formallySmooth_residueField := by
    have e : (IsLocalRing.ResidueField.instAlgebra :
        Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) =
        Algebra.id (IsLocalRing.ResidueField R) := by
      apply Algebra.algebra_ext
      intro x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rfl
    have h : @Algebra.FormallySmooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R) _ _
        (Algebra.id (IsLocalRing.ResidueField R)) := inferInstance
    convert h

section PointGenericFibre

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {K' : Type u} [CommRing K'] [Algebra R' K'] [Algebra R K'] [IsScalarTower R R' K']
  [Algebra K K'] [IsScalarTower R K K']

theorem specMap_algebraMap_comp_specMap_algebraMap (R K R' K' : Type u) [CommRing R] [Field K]
    [Algebra R K] [CommRing R'] [Algebra R R'] [CommRing K'] [Algebra R' K'] [Algebra R K']
    [IsScalarTower R R' K'] [Algebra K K'] [IsScalarTower R K K'] :
    Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

def pointGenericFibre (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K')))
      (pullback.snd f (specGenericFibreInclusion R K)) :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ x.1)
      (Spec.map (CommRingCat.ofHom (algebraMap K K')))
      (by rw [Category.assoc, x.2, specGenericFibreInclusion_eq,
            specMap_algebraMap_comp_specMap_algebraMap R K R' K']),
    pullback.lift_snd _ _ _⟩

@[simp]
theorem pointGenericFibre_coe_comp_fst
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f) :
    (pointGenericFibre (K := K) (K' := K') x).1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ x.1 :=
  pullback.lift_fst _ _ _

@[simp]
theorem pointGenericFibre_coe_comp_snd
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f) :
    (pointGenericFibre (K := K) (K' := K') x).1 ≫ pullback.snd f (specGenericFibreInclusion R K) =
      Spec.map (CommRingCat.ofHom (algebraMap K K')) :=
  pullback.lift_snd _ _ _

end PointGenericFibre


def ModelFamily.CatchesIndexOnePoints {R K : Type u} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} (M : ModelFamily R K gK) : Prop :=
  ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    (K' : Type u) [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra R K'] [IsScalarTower R R' K']
    [Algebra K K'] [IsScalarTower R K K'],
    IsIndexOneExtension R R' →
    ∀ a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K K'))) gK,
      ∃ (i : M.ι) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (M.str i)),
        schemeHomOverComp (pointGenericFibre x) (M.chart i) = a

section Gates

variable (R K : Type u) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]

def ModelFamily.trivial : ModelFamily R K (𝟙 (Spec (CommRingCat.of K))) where
  ι := PUnit
  X := fun _ => Spec (CommRingCat.of R)
  str := fun _ => 𝟙 _
  chart := fun _ => ⟨pullback.snd (𝟙 _) (specGenericFibreInclusion R K), Category.comp_id _⟩
  isOpenImmersion_chart := fun _ => inferInstance

theorem gate_catchesIndexOnePoints_trivial : (ModelFamily.trivial R K).CatchesIndexOnePoints := by
  intro R' _ _ _ _ _ K' _ _ _ _ _ _ _ _ a
  refine ⟨PUnit.unit, ⟨Spec.map (CommRingCat.ofHom (algebraMap R R')), Category.comp_id _⟩, ?_⟩
  exact (subsingleton_schemeHomOver_of_isIso (Spec.map (CommRingCat.ofHom (algebraMap K K')))
    (𝟙 (Spec (CommRingCat.of K)))).allEq _ _

def ModelFamily.empty {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K)) : ModelFamily R K gK where
  ι := PEmpty
  X := fun i => i.elim
  str := fun i => i.elim
  chart := fun i => i.elim
  isOpenImmersion_chart := fun i => i.elim

theorem gate_not_catchesIndexOnePoints_empty [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) gK) :
    ¬ (ModelFamily.empty R K gK).CatchesIndexOnePoints := by
  intro h
  have ha : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _
  obtain ⟨i, -, -⟩ := h R K (IsIndexOneExtension.refl R) ⟨a.1, by rw [ha]; exact a.2⟩
  exact i.elim

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
