import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

structure PartialAction (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) where

  dom : (pullback f p).Opens

  dense_dom : Dense (dom : Set ↥(pullback f p))

  hom : (dom : Scheme.{u}) ⟶ P

  hom_comp : hom ≫ p = dom.ι ≫ pullback.snd f p ≫ p

namespace PartialAction

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

abbrev pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
    (x : SchemeHomOver t p) : T ⟶ pullback f p :=
  pullback.lift γ.1 x.1 (γ.2.trans x.2.symm)

def Defined (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) : Prop :=
  Set.range (pair γ x) ⊆ (a.dom : Set ↥(pullback f p))

def liftDom (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    T ⟶ (a.dom : Scheme.{u}) :=
  IsOpenImmersion.lift a.dom.ι (pair γ x) (by rw [Scheme.Opens.range_ι]; exact hd)

@[simp]
theorem liftDom_ι (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.liftDom γ x hd ≫ a.dom.ι = pair γ x :=
  IsOpenImmersion.lift_fac _ _ _

theorem liftDom_hom_comp (a : PartialAction k f p) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f) (x : SchemeHomOver t p)
    (hd : a.Defined γ x) : (a.liftDom γ x hd ≫ a.hom) ≫ p = t := by
  rw [Category.assoc, a.hom_comp, ← Category.assoc (a.liftDom γ x hd), liftDom_ι,
    ← Category.assoc, pullback.lift_snd]
  exact x.2

def act (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) : SchemeHomOver t p :=
  ⟨a.liftDom γ x hd ≫ a.hom, a.liftDom_hom_comp γ x hd⟩

@[simp]
theorem act_coe (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    (a.act γ x hd).1 = a.liftDom γ x hd ≫ a.hom :=
  rfl

def UnitActs (a : PartialAction k f p) (L : RelativeGroupLaw k f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t p)
    (hd : a.Defined (L.one t) x), a.act (L.one t) x hd = x

def Assoc (a : PartialAction k f p) (L : RelativeGroupLaw k f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ δ : SchemeHomOver t f)
    (x : SchemeHomOver t p) (hd₁ : a.Defined δ x) (hd₂ : a.Defined γ (a.act δ x hd₁)),
    ∃ hd₃ : a.Defined (L.mul t γ δ) x, a.act γ (a.act δ x hd₁) hd₂ = a.act (L.mul t γ δ) x hd₃

def modelPoint {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (v : SchemeHomOver t (V.ι ≫ f)) : SchemeHomOver t p :=
  ⟨v.1 ≫ ι, by rw [Category.assoc, hι]; exact v.2⟩

@[simp]
theorem modelPoint_coe {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (v : SchemeHomOver t (V.ι ≫ f)) :
    (modelPoint ι hι v).1 = v.1 ≫ ι :=
  rfl

def Compatible (a : PartialAction k f p) (L : RelativeGroupLaw k f) (V : G.Opens)
    (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f)
    (v w : SchemeHomOver t (V.ι ≫ f)),
    NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul t γ (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) →
    ∃ hd : a.Defined γ (modelPoint ι hι v), a.act γ (modelPoint ι hι v) hd = modelPoint ι hι w

def Maximal (a : PartialAction k f p) : Prop :=
  ∀ (U' : (pullback f p).Opens) (h' : (U' : Scheme.{u}) ⟶ P) (hle : a.dom ≤ U'),
    (pullback f p).homOfLE hle ≫ h' = a.hom → U' = a.dom

def Stable (a : PartialAction k f p) (W : Set ↥P) : Prop :=
  ∀ z : ↥(a.dom : Scheme.{u}), pullback.snd f p (a.dom.ι z) ∈ W → a.hom z ∈ W

end PartialAction

end GoodReductionJacobian

end
