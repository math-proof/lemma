module

public import Structure.CerednikDrinfeld_QMFineModuli
public import Def.CerednikDrinfeld_QMIsogeny
public import Def.CerednikDrinfeld_QMFormalModuleOf
public import Def.CerednikDrinfeld_QMModuliProps
public import Structure.CerednikDrinfeld_QMRigidification
public import Abbrev.CerednikDrinfeld_QMRigidification

public section

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}


public theorem iso_iff_exists_via {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S) :
    Iso E E' ↔ ∃ (i : E.A ≅ E'.A) (hi : i.hom ≫ E'.f = E.f), IsoVia E E' i hi := Iff.rfl


public theorem isAtkinLehnerQuotient_iff_exists_via {S : Type} [CommRing S] (r : ℕ) (E E' : FakeEllipticCurve Λ N S) :
    IsAtkinLehnerQuotient r E E' ↔ ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A) (hψ : ψ ≫ E.f = E'.f),
      IsAtkinLehnerQuotientVia r E E' φ hφ ψ hψ := Iff.rfl


public theorem isLevelIsogeny_iff_exists_via {S : Type} [CommRing S] (ℓ : ℕ) (u : WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S) :
    IsLevelIsogeny ℓ u d ↔ ∃ (φ : u.1.A ⟶ d.A) (hφ : φ ≫ d.f = u.1.f) (ψ : d.A ⟶ u.1.A) (hψ : ψ ≫ u.1.f = d.f),
      IsLevelIsogenyVia ℓ u d φ hφ ψ hψ := Iff.rfl


namespace Rigidification

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}

