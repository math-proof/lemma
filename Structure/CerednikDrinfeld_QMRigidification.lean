import Structure.CerednikDrinfeld_QMFineModuli
import Def.CerednikDrinfeld_QMIsogeny
import Structure.CerednikDrinfeld_QMFormalModuleOf
import Structure.CerednikDrinfeld_QMModuliProps

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}


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


end Rigidification


end CerednikDrinfeld.QM.FakeEllipticCurve
