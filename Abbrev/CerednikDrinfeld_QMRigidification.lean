module

public import Structure.CerednikDrinfeld_QMFineModuli
public import Def.CerednikDrinfeld_QMIsogeny
public import Structure.CerednikDrinfeld_QMFormalModuleOf
public import Structure.CerednikDrinfeld_QMModuliProps
public import Structure.CerednikDrinfeld_QMRigidification

@[expose] public section

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}


namespace Rigidification

variable {r : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
  {B : Type} [CommRing B] [Algebra 𝒪 B] {ψ : Onr →ₐ[𝒪] B} {E : FakeEllipticCurve Λ N B}


abbrev residueLeg {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) :
    (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) →+* (B ⧸ Ideal.span {algebraMap 𝒪 B π}) :=
  Ideal.quotientMap (Ideal.span {algebraMap 𝒪 B π}) (ψ : Onr →+* B)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
      (by rw [show (ψ : Onr →+* B) (algebraMap 𝒪 Onr π) = algebraMap 𝒪 B π from ψ.commutes π]
          exact Ideal.subset_span rfl))))

end Rigidification

abbrev RigidifiedCurve (r : ℕ) {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : Type 1 :=
  Σ E : FakeEllipticCurve Λ N B, Rigidification r π A₀ ψ E

end CerednikDrinfeld.QM.FakeEllipticCurve
