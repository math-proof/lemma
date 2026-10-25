import Lemma.CerednikDrinfeld.QMRigidification
import Structure.CerednikDrinfeld_QMFineModuli
import Lemma.CerednikDrinfeld.QMFineModuliT
import Def.CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Structure.CerednikDrinfeld_RigidifiedPairClassModel

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace CerednikDrinfeld.QM.RigidifiedPairClass


theorem Pt.ext' {C : Type} [CommRing C] {πC : C} {MC : Scheme.{0}} {g : MC ⟶ Spec (CommRingCat.of C)}
    {X : ℕ → Scheme.{0}} {ξ : ∀ d, X d ⟶ MC} {T : Type} [CommRing T] [Algebra C T]
    (p q : Pt πC g X ξ T) (ht : p.t = q.t) (hd : p.d = q.d) (hx : p.x ≫ eqToHom (congrArg X hd) = q.x) : p = q := by
  obtain ⟨pt, pht, pd, px, phx⟩ := p
  obtain ⟨qt, qht, qd, qx, qhx⟩ := q
  cases ht; cases hd
  simp only [eqToHom_refl, Category.comp_id] at hx
  cases hx
  rfl

theorem span_le_comap {C : Type} [CommRing C] (πC : C) {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T']
    (φ : T →ₐ[C] T') :
    Ideal.span {algebraMap C T πC} ≤ (Ideal.span {algebraMap C T' πC}).comap (φ : T →+* T') := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
  have : (φ : T →+* T') (algebraMap C T πC) = algebraMap C T' πC := φ.commutes πC
  rw [this]
  exact Ideal.subset_span rfl

def qmap {C : Type} [CommRing C] (πC : C) {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T']
    (φ : T →ₐ[C] T') : (T ⧸ Ideal.span {algebraMap C T πC}) →+* (T' ⧸ Ideal.span {algebraMap C T' πC}) :=
  Ideal.quotientMap _ (φ : T →+* T') (span_le_comap πC φ)

theorem qmap_comp_mk {C : Type} [CommRing C] (πC : C) {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T']
    (φ : T →ₐ[C] T') :
    (qmap πC φ).comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp (φ : T →+* T') := by
  ext x; rfl

theorem qmap_id {C : Type} [CommRing C] (πC : C) {T : Type} [CommRing T] [Algebra C T] :
    qmap πC (AlgHom.id C T) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  ext x; rfl

theorem qmap_comp {C : Type} [CommRing C] (πC : C) {T₁ T₂ T₃ : Type} [CommRing T₁] [Algebra C T₁] [CommRing T₂] [Algebra C T₂]
    [CommRing T₃] [Algebra C T₃] (φ : T₁ →ₐ[C] T₂) (φ' : T₂ →ₐ[C] T₃) :
    qmap πC (φ'.comp φ) = (qmap πC φ').comp (qmap πC φ) := by
  apply Ideal.Quotient.ringHom_ext
  ext x; rfl

noncomputable def Pt.map {C : Type} [CommRing C] {πC : C} {MC : Scheme.{0}} {g : MC ⟶ Spec (CommRingCat.of C)}
    {X : ℕ → Scheme.{0}} {ξ : ∀ d, X d ⟶ MC} {T T' : Type} [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T']
    (φ : T →ₐ[C] T') (p : Pt πC g X ξ T) : Pt πC g X ξ T' where
  t := Spec.map (CommRingCat.ofHom (φ : T →+* T')) ≫ p.t
  ht := by
    rw [Category.assoc, p.ht, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap
  d := p.d
  x := Spec.map (CommRingCat.ofHom (qmap πC φ)) ≫ p.x
  hx := by
    rw [Category.assoc, p.hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, qmap_comp_mk]

theorem Pt.map_id {C : Type} [CommRing C] {πC : C} {MC : Scheme.{0}} {g : MC ⟶ Spec (CommRingCat.of C)}
    {X : ℕ → Scheme.{0}} {ξ : ∀ d, X d ⟶ MC} {T : Type} [CommRing T] [Algebra C T] (p : Pt πC g X ξ T) :
    p.map (AlgHom.id C T) = p := by
  refine Pt.ext' (p.map (AlgHom.id C T)) p ?_ rfl ?_
  · show Spec.map (CommRingCat.ofHom (RingHom.id T)) ≫ p.t = p.t
    rw [CommRingCat.ofHom_id]; erw [Spec.map_id]; exact Category.id_comp _
  · show (Spec.map (CommRingCat.ofHom (qmap πC (AlgHom.id C T))) ≫ p.x) ≫ eqToHom rfl = p.x
    rw [qmap_id, CommRingCat.ofHom_id]; erw [Spec.map_id]; simp

theorem Pt.map_comp {C : Type} [CommRing C] {πC : C} {MC : Scheme.{0}} {g : MC ⟶ Spec (CommRingCat.of C)}
    {X : ℕ → Scheme.{0}} {ξ : ∀ d, X d ⟶ MC} {T₁ T₂ T₃ : Type} [CommRing T₁] [Algebra C T₁] [CommRing T₂] [Algebra C T₂]
    [CommRing T₃] [Algebra C T₃] (φ : T₁ →ₐ[C] T₂) (φ' : T₂ →ₐ[C] T₃) (p : Pt πC g X ξ T₁) :
    p.map (φ'.comp φ) = (p.map φ).map φ' := by
  refine Pt.ext' (p.map (φ'.comp φ)) ((p.map φ).map φ') ?_ rfl ?_
  · show Spec.map (CommRingCat.ofHom ((φ'.comp φ : T₁ →ₐ[C] T₃) : T₁ →+* T₃)) ≫ p.t =
      Spec.map (CommRingCat.ofHom (φ' : T₂ →+* T₃)) ≫ (Spec.map (CommRingCat.ofHom (φ : T₁ →+* T₂)) ≫ p.t)
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  · show (Spec.map (CommRingCat.ofHom (qmap πC (φ'.comp φ))) ≫ p.x) ≫ eqToHom rfl =
      Spec.map (CommRingCat.ofHom (qmap πC φ')) ≫ (Spec.map (CommRingCat.ofHom (qmap πC φ)) ≫ p.x)
    rw [eqToHom_refl, Category.comp_id, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, qmap_comp]

section Model

variable {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
  (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
  {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)

  (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
    FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) g)

  (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
    { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
      x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })

theorem quotEquiv_comp_mk {C : Type} [CommRing C] (πC : C) (T : Type) [CommRing T] [Algebra C T]
    (h0 : algebraMap C T πC = 0) :
    (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom).comp
      (Ideal.Quotient.mk (Ideal.span {algebraMap C T πC})) = RingHom.id T := by
  ext t
  rfl

noncomputable def ptX (d : ℕ) (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (hψT : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1)
    (hd : ρ.d = d) (h0 : algebraMap C T (algebraMap 𝒪 C π) = 0) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ g) :=
  ⟨Spec.map (CommRingCat.ofHom
      (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr h0)).trans (RingEquiv.quotientBot T)).toRingHom)) ≫
      (xOf T ψT hψT u ρ).1 ≫ eqToHom (congrArg X hd), by
    subst hd
    simp only [eqToHom_refl, Category.comp_id, Category.assoc]
    rw [reassoc_of% (xOf T ψT hψT u ρ).2, (tM T u).2]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, quotEquiv_comp_mk (algebraMap 𝒪 C π) T h0,
      CommRingCat.ofHom_id]
    erw [Spec.map_id]
    exact Category.id_comp _⟩

def RelLoc (T : Type) [CommRing T] [Algebra C T]
    (p q : Pt (algebraMap 𝒪 C π) g X ξ T) : Prop :=
  ∃ (m : ℕ) (f : Fin m → (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})),
    Ideal.span (Set.range f) = ⊤ ∧
    ∀ k : Fin m,
      ∃ (L : Type) (_ : CommRing L) (_ : Algebra (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)
        (_ : IsLocalization.Away (f k) L) (_ : Algebra C L)
        (_ : IsScalarTower C (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)
        (_ : Algebra 𝒪 L) (_ : IsScalarTower 𝒪 C L)
        (h0 : algebraMap C L (algebraMap 𝒪 C π) = 0)
        (u u' : FakeEllipticCurve.WithFullLevel Λ N n L)
        (ρ : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u.1)
        (ρ' : FakeEllipticCurve.Rigidification r π A₀ ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) u'.1)
        (hd : ρ.d = p.d) (hd' : ρ'.d = q.d)
        (i₀ : u.1.A ≅ u'.1.A) (hi : i₀.hom ≫ u'.1.f = u.1.f) (_ : FakeEllipticCurve.WithFullLevel.IsoVia u u' i₀ hi)
        (_ : (∃ (ib : ρ.Eb.A ⟶ ρ'.Eb.A) (_ : ib ≫ ρ'.gb = ρ.gb ≫ i₀.hom) (_ : ib ≫ ρ'.Eb.f = ρ.Eb.f)
            (uA : ρ'.Ab.A ⟶ ρ.Ab.A) (_ : FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ.Ab ρ'.Ab uA) (_ : uA ≫ ρ.gA = ρ'.gA)
            (i₁ j₁ : ℕ),
            ib ≫ ρ'.φ ≫ uA ≫ ρ.Ab.act ⟨(((r ^ i₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ.φ ≫ ρ.Ab.act ⟨(((r ^ j₁ : ℕ) : ℤ) : ℚ), hΛℤ _⟩)),
        (ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf p.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl u ρ hd h0).1 =
            Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)) ≫ p.x ∧
          (ptX 𝒪 π Onr Λ A₀ n C ψ g X ξ tM xOf q.d L ((IsScalarTower.toAlgHom 𝒪 C L).comp ψ) rfl u' ρ' hd' h0).1 =
            Spec.map (CommRingCat.ofHom (algebraMap (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}) L)) ≫ q.x

def Rel (T : Type) [CommRing T] [Algebra C T] (p q : Pt (algebraMap 𝒪 C π) g X ξ T) : Prop :=
  p.t = q.t ∧ RelLoc 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf T p q

def MapCompat : Prop :=
  ∀ (T T' : Type) [CommRing T] [Algebra C T] [CommRing T'] [Algebra C T'] (φ : T →ₐ[C] T')
    (p q : Pt (algebraMap 𝒪 C π) g X ξ T),
    Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf T p q → Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf T' (p.map φ) (q.map φ)

noncomputable def PR (hmap : MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf) : CerednikDrinfeld.FormalOmega.AlgFunctor C where
  obj T _ _ := Quot (Rel 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf T)
  map {T} _ _ {T'} _ _ φ := Quot.map (Pt.map φ) (fun p q h => hmap T T' φ p q h)
  map_id {T} _ _ z := by
    induction z using Quot.ind with
    | mk p => exact congrArg (Quot.mk _) (Pt.map_id p)
  map_comp {T₁} _ _ {T₂} _ _ {T₃} _ _ φ φ' z := by
    induction z using Quot.ind with
    | mk p => exact congrArg (Quot.mk _) (Pt.map_comp φ φ' p)

noncomputable def toM (hmap : MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf) (S : Type) [CommRing S] [Algebra C S]
    (z : (PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap).obj S) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) g :=
  Quot.lift (fun p : Pt (algebraMap 𝒪 C π) g X ξ S =>
      (⟨p.t, p.ht⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C S))) g))
    (fun _ _ h => Subtype.ext h.1) z

noncomputable def pt (hmap : MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf) (d : ℕ) (T : Type) [CommRing T] [Algebra C T]
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) (ξ d ≫ g)) :
    (PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap).obj T :=
  Quot.mk _
    { t := x.1 ≫ ξ d, ht := by rw [Category.assoc]; exact x.2, d := d,
      x := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ x.1, hx := by rw [Category.assoc] }

noncomputable def ptR (hmap : MapCompat 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf)
    (S : Type) [CommRing S] [Algebra C S] [Algebra 𝒪 S] [IsScalarTower 𝒪 C S]
    (ψS : Onr →ₐ[𝒪] S) (hψS : ψS = (IsScalarTower.toAlgHom 𝒪 C S).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n S) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψS u.1) :
    (PR 𝒪 π Onr Λ hΛℤ A₀ n C ψ g X ξ tM xOf hmap).obj S :=
  Quot.mk _
    { t := (tM S u).1, ht := (tM S u).2, d := ρ.d, x := (xOf S ψS hψS u ρ).1, hx := (xOf S ψS hψS u ρ).2 }

end Model

end CerednikDrinfeld.QM.RigidifiedPairClass
