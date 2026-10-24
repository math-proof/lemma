import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.DescentCharacter

variable {X Y : Scheme.{u}}

def transportIso {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (M : Y.Modules) :
    (Scheme.Modules.pullback T).obj ((Scheme.Modules.pullback q).obj M) ≅ (Scheme.Modules.pullback q).obj M :=
  (Scheme.Modules.pullbackComp T q).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

def transportNatIso {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) :
    Scheme.Modules.pullback q ⋙ Scheme.Modules.pullback T ≅ Scheme.Modules.pullback q :=
  Scheme.Modules.pullbackComp T q ≪≫ Scheme.Modules.pullbackCongr h

theorem transportNatIso_app {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (M : Y.Modules) :
    (transportNatIso h).app M = transportIso h M := rfl

def translateIso {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M :=
  (transportIso h N).symm ≪≫ (Scheme.Modules.pullback T).mapIso β ≪≫ transportIso h M

def discrepancy {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj M :=
  β.symm ≪≫ translateIso h β

variable {R : Type u} [CommRing R]

def baseSection (f : X ⟶ Spec (CommRingCat.of R)) (c : R) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top (a := U))).op (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))

def baseSectionRingHom (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (le_top (a := U))).op).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

@[simp] theorem baseSectionRingHom_apply (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (c : R) :
    baseSectionRingHom f U c = baseSection f c U := rfl

@[simp] theorem baseSection_one (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : baseSection f 1 U = 1 := by
  rw [← baseSectionRingHom_apply, map_one]

@[simp] theorem baseSection_mul (f : X ⟶ Spec (CommRingCat.of R)) (c c' : R) (U : X.Opens) :
    baseSection f (c * c') U = baseSection f c U * baseSection f c' U := by
  simp only [← baseSectionRingHom_apply, map_mul]

theorem map_baseSection (f : X ⟶ Spec (CommRingCat.of R)) (c : R) {U V : X.Opens} (i : V ⟶ U) :
    X.presheaf.map i.op (baseSection f c U) = baseSection f c V := by
  unfold baseSection
  rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
  rfl

def IsBaseScalar (f : X ⟶ Spec (CommRingCat.of R)) {M : X.Modules} (σ : M ⟶ M) (c : R) : Prop :=
  ∀ (U : X.Opens) (s : Γ(M, U)), σ.app U s = baseSection f c U • s

def HasValue (f : X ⟶ Spec (CommRingCat.of R)) {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) (c : R) : Prop :=
  IsBaseScalar f (discrepancy h β).hom c

def IsCharValue (f : X ⟶ Spec (CommRingCat.of R)) {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (N M : Y.Modules)
    (c : R) : Prop :=
  ∃ β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M, HasValue f h β c

end AlgebraicGeometry.DescentCharacter

end
