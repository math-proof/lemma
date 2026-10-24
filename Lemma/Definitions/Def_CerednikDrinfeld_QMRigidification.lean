import Lemma.Definitions.Def_CerednikDrinfeld_QMFineModuli
import Lemma.Definitions.Def_CerednikDrinfeld_QMIsogeny
import Lemma.Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Lemma.Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def IsoVia {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S) (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt i.hom hi (E.L.mul t P Q) = E'.L.mul t (mapPt i.hom hi P) (mapPt i.hom hi Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ i.hom = i.hom ≫ E'.act x) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P ↔ FactorsThrough E'.lev (mapPt i.hom hi P))

theorem iso_iff_exists_via {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S) :
    Iso E E' ↔ ∃ (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f), IsoVia E E' i hi := Iff.rfl

def IsAtkinLehnerQuotientVia {S : Type} [CommRing S] (r : ℕ) (E E' : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧ (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ hr : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩ ∧ ψ ≫ φ = E'.act ⟨((r : ℚ) : ℍ[ℚ, a, b]), hr⟩) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E'.L.one t ↔
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (E.act m) (E.act_over m) P = E.L.one t) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P))

theorem isAtkinLehnerQuotient_iff_exists_via {S : Type} [CommRing S] (r : ℕ) (E E' : FakeEllipticCurve Λ N S) :
    IsAtkinLehnerQuotient r E E' ↔ ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f),
      IsAtkinLehnerQuotientVia r E E' φ hφ ψ hψ := Iff.rfl

def IsLevelIsogenyVia {S : Type} [CommRing S] (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S)
    (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = d.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt φ hφ (u.1.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t d.f),
      mapPt ψ hψ (d.L.mul t P Q) = u.1.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ φ = φ ≫ d.act x) ∧ (∀ x : ↥Λ, d.act x ≫ ψ = ψ ≫ u.1.act x) ∧
    (∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = u.1.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = d.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      mapPt φ hφ P = d.L.one t ↔ FactorsThrough u.2.levK P) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P → FactorsThrough d.lev (mapPt φ hφ P))

theorem isLevelIsogeny_iff_exists_via {S : Type} [CommRing S] (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S) :
    IsLevelIsogeny ℓ u d ↔ ∃ (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = d.f),
      IsLevelIsogenyVia ℓ u d φ hφ ψ hψ := Iff.rfl

structure Rigidification (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (E : FakeEllipticCurve Λ N B) : Type 1 where

  Eb : FakeEllipticCurve Λ N (B ⧸ Ideal.span {algebraMap 𝒪 B π})

  gb : Eb.A ⟶ E.A

  isPullback_Eb : FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) E Eb gb

  Ab : FakeEllipticCurve Λ N (B ⧸ Ideal.span {algebraMap 𝒪 B π})

  gA : Ab.A ⟶ A₀.A

  isPullback_Ab : FakeEllipticCurve.IsPullbackVia
    (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B π}) (ψ : Onr →+* B)
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
        (by rw [show (ψ : Onr →+* B) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 B π from ψ.commutes π]
            exact Ideal.subset_span rfl)))))
    A₀ Ab gA

  d : ℕ

  φ : Eb.A ⟶ Ab.A

  φ' : Ab.A ⟶ Eb.A

  φ_over : φ ≫ Ab.f = Eb.f

  isIsogenyPair : FakeEllipticCurve.IsIsogenyPair (r ^ d) Eb Ab φ φ'

  preservesLevel : FakeEllipticCurve.PreservesLevel Eb Ab φ φ_over

namespace Rigidification

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

def IsComparison (ρ₁ ρ₂ : Rigidification r π A₀ ψ E) (u : ρ₂.Eb.A ⟶ ρ₁.Eb.A) (uA : ρ₂.Ab.A ⟶ ρ₁.Ab.A) : Prop :=
  FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₁.Eb ρ₂.Eb u ∧ u ≫ ρ₁.gb = ρ₂.gb ∧
  FakeEllipticCurve.IsPullbackVia (RingHom.id _) ρ₁.Ab ρ₂.Ab uA ∧ uA ≫ ρ₁.gA = ρ₂.gA

def Equiv (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (ρ₁ ρ₂ : Rigidification r π A₀ ψ E) : Prop :=
  ∃ (u : ρ₂.Eb.A ⟶ ρ₁.Eb.A) (uA : ρ₂.Ab.A ⟶ ρ₁.Ab.A), IsComparison ρ₁ ρ₂ u uA ∧
    ∃ i j : ℕ, u ≫ ρ₁.φ ≫ ρ₁.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩

def IsTranslateBy (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (eγ : A₀.A ⟶ A₀.A) (ρ₁ ρ₂ : Rigidification r π A₀ ψ E) : Prop :=
  ∃ (u : ρ₂.Eb.A ⟶ ρ₁.Eb.A) (uA : ρ₂.Ab.A ⟶ ρ₁.Ab.A), IsComparison ρ₁ ρ₂ u uA ∧
    ∃ (eγb : ρ₁.Ab.A ⟶ ρ₁.Ab.A), eγb ≫ ρ₁.gA = ρ₁.gA ≫ eγ ∧ eγb ≫ ρ₁.Ab.f = ρ₁.Ab.f ∧
      ∃ i j : ℕ, u ≫ ρ₁.φ ≫ eγb ≫ ρ₁.Ab.act ⟨(((r ^ i : ℕ) : ℤ) : ℚ), hΛℤ _⟩ = ρ₂.φ ≫ uA ≫ ρ₁.Ab.act ⟨(((r ^ j : ℕ) : ℤ) : ℚ), hΛℤ _⟩

def IsPullbackVia {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {E' : FakeEllipticCurve Λ N B'} (g : E'.A ⟶ E.A) (_hE' : FakeEllipticCurve.IsPullbackVia (f : B →+* B') E E' g)
    (ρ : Rigidification r π A₀ ψ E) (ρ' : Rigidification r π A₀ (f.comp ψ) E') : Prop :=
  ∃ (ub : ρ'.Eb.A ⟶ ρ.Eb.A) (uA : ρ'.Ab.A ⟶ ρ.Ab.A),
    FakeEllipticCurve.IsPullbackVia
        (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (f : B →+* B')
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (f : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from f.commutes π]
                exact Ideal.subset_span rfl)))))
        ρ.Eb ρ'.Eb ub ∧
      ub ≫ ρ.gb = ρ'.gb ≫ g ∧
    FakeEllipticCurve.IsPullbackVia
        (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B' π}) (f : B →+* B')
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
            (by rw [show (f : B →+* B') (algebraMap 𝒪 B π) = algebraMap 𝒪 B' π from f.commutes π]
                exact Ideal.subset_span rfl)))))
        ρ.Ab ρ'.Ab uA ∧
      uA ≫ ρ.gA = ρ'.gA ∧
    ρ'.d = ρ.d ∧ ub ≫ ρ.φ = ρ'.φ ≫ uA

abbrev residueLeg {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) :
    (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (B ⧸ Ideal.span {algebraMap 𝒪 B π}) :=
  Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B π}) (ψ : Onr →+* B)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
      (by rw [show (ψ : Onr →+* B) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 B π from ψ.commutes π]
          exact Ideal.subset_span rfl))))

def IsRigTransport {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    (θ₀ : GoodReductionJacobian.RelativeGroupLaw.FormalCoordinates A₀.f 2)
    (κ : (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (Onr ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r Onr))
    (β₀ : CerednikDrinfeld.SpecialFormal.Series (Onr ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r Onr))
    {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}
    (ρ : Rigidification r π A₀ ψ E) (θ : GoodReductionJacobian.RelativeGroupLaw.FormalCoordinates E.f 2) (j : ℕ)
    {Φ : CerednikDrinfeld.FormalODModule r (Onr ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r Onr)}
    (t : CerednikDrinfeld.SpecialFormal.Rigidified r Φ B) : Prop :=
  ∃ (κB : (B ⧸ Ideal.span {algebraMap 𝒪 B π}) →+* (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B))
    (σ : CerednikDrinfeld.SpecialFormal.Series (B ⧸ Ideal.span {algebraMap 𝒪 B π})),

    κB.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 B π})) = Ideal.Quotient.mk (CerednikDrinfeld.SpecialFormal.pIdeal r B) ∧
    κB.comp (residueLeg π ψ) = (CerednikDrinfeld.SpecialFormal.residueMap (ψ : Onr →+* B)).comp κ ∧

    (∀ (B'' : Type) [CommRing B''] [Algebra (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B''] [Algebra B B'']
        [Algebra (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B''],
        algebraMap B B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (Ideal.Quotient.mk _) →
        algebraMap (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B'' = (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'').comp (residueLeg π ψ) →
        ∀ (J : Ideal B'') (m : ℕ), J ^ (m + 1) = ⊥ → ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          ∀ PA : Spec (CommRingCat.of B'') ⟶ ρ.Ab.A,
            PA ≫ ρ.Ab.f = Spec.map (CommRingCat.ofHom (algebraMap (B ⧸ Ideal.span {algebraMap 𝒪 B π}) B'')) →
            PA ≫ ρ.gA = (θ₀ B'' s).1 →
              PA ≫ ρ.φ' ≫ ρ.gb = (θ B'' (fun i => MvFormalGroup.nilEval m (σ i) s)).1) ∧

    t.ρ = (CerednikDrinfeld.SpecialFormal.Series.map κB σ).comp
      ((CerednikDrinfeld.SpecialFormal.Series.map (CerednikDrinfeld.SpecialFormal.residueMap (ψ : Onr →+* B)) β₀).comp
        (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ CerednikDrinfeld.SpecialFormal.pIdeal r B)) ^ (r ^ j)))

end Rigidification

abbrev RigidifiedCurve (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : Type 1 :=
  Σ E : FakeEllipticCurve Λ N B, Rigidification r π A₀ ψ E

end CerednikDrinfeld.QM.FakeEllipticCurve
