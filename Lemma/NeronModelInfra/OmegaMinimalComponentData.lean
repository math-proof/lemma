import Mathlib
import Lemma.NeronModelInfra.WeakNeronModel
import Lemma.AlgebraicGeometry.KaehlerModule
import Lemma.NeronModelInfra.TopFormOrder
import Lemma.NeronModelInfra.SmoothnessDefect
import Structure.NeronModelInfra_OmegaMinimalComponentData

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace NeronModelInfra

section StalkAlgebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (y : Y)

theorem ofHom_stalkAlgebraMap_eq :
    CommRingCat.ofHom (stalkAlgebraMap f y) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial) ≫ f.stalkMap y := by
  ext r
  change stalkAlgebraMap f y r = _
  rw [stalkAlgebraMap_apply]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra :
    letI := stalkAlgebra f y
    Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))) := by
  letI := stalkAlgebra f y
  change Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (stalkAlgebraMap f y))
  rw [ofHom_stalkAlgebraMap_eq, Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk f,
    Spec.fromSpecStalk_eq]

end StalkAlgebra

section Reading

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ(gK.topDifferentials d, ⊤))


variable {R K gK d ω}

def ComponentReading.n (T : ComponentReading R K gK d ω) : ℤ :=
  TopFormOrder.addOrd (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) T.a

end Reading

section Minimal

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ(gK.topDifferentials d, ⊤))


variable {R K gK d ω}

def MinimalComponentData.IsOmegaMinimal (D : MinimalComponentData R K gK d ω) : Prop :=
  (∀ (c : D.ι) (T : ComponentReading R K gK d ω), (D.C c).n ≤ T.n) ∧
  (∀ T : ComponentReading R K gK d ω, (∃ c : D.ι, T.n = (D.C c).n) →
    ∃ (c : D.ι) (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (D.C c).f),
      IsOpenImmersion ε.1 ∧ ε.1.base ⟨T.y, hyW⟩ = (D.C c).y ∧
      (genericFibreRestrict R K (D.C c).f (W.ι ≫ T.f) ε).1 ≫ (D.C c).e.1 =
        (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)

end Minimal

section Gates

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ} {ω : Γ(gK.topDifferentials d, ⊤)}

theorem ComponentReading.n_eq_one_of_a_eq_uniformizer (T : ComponentReading R K gK d ω)
    (ϖ : T.Y.presheaf.stalk T.y) (hϖ : IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y) = Ideal.span {ϖ})
    (h : T.a = algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) ϖ) :
    T.n = 1 := by
  unfold ComponentReading.n
  rw [h]
  exact TopFormOrder.addOrd_uniformizer _ _ ϖ hϖ

theorem ComponentReading.n_eq_two_of_a_eq_uniformizer_sq (T : ComponentReading R K gK d ω)
    (ϖ : T.Y.presheaf.stalk T.y) (hϖ : IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y) = Ideal.span {ϖ})
    (h : T.a = algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) ϖ ^ 2) :
    T.n = 2 := by
  unfold ComponentReading.n
  rw [h]
  exact TopFormOrder.addOrd_uniformizer_sq _ _ ϖ hϖ

theorem MinimalComponentData.IsOmegaMinimal.n_eq (D : MinimalComponentData R K gK d ω)
    (hD : D.IsOmegaMinimal) (c c' : D.ι) : (D.C c).n = (D.C c').n :=
  le_antisymm (hD.1 c (D.C c')) (hD.1 c' (D.C c))

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
