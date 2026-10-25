import Mathlib.Algebra.CharP.Frobenius
import Def.CerednikDrinfeld_QMModuliProps
import Structure.CerednikDrinfeld_FakeEllipticFrobenius

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]


namespace FrobeniusVerschiebungData

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP S ℓ] {E Eℓ : FakeEllipticCurve Λ N S}

theorem isPullback (D : FrobeniusVerschiebungData ℓ E Eℓ) : IsPullback (frobenius S ℓ) E Eℓ :=
  ⟨D.pr, D.pr_isPullback, D.pr_mul, D.pr_act, D.pr_lev⟩

def FPt (D : FrobeniusVerschiebungData ℓ E Eℓ) : SchemeHomOver E.f Eℓ.f := ⟨D.F, D.F_over⟩

def VPt (D : FrobeniusVerschiebungData ℓ E Eℓ) : SchemeHomOver Eℓ.f E.f := ⟨D.V, D.V_over⟩

end FrobeniusVerschiebungData

def HasFrobeniusVerschiebung (ℓ : ℕ) [Fact ℓ.Prime] [CharP S ℓ] (E Eℓ : FakeEllipticCurve Λ N S) : Prop :=
  Nonempty (FrobeniusVerschiebungData ℓ E Eℓ)

def IsFrobeniusKernel {ℓ : ℕ} [Fact ℓ.Prime] [CharP S ℓ] {Eℓ : FakeEllipticCurve Λ N S}
    (u : WithExtraLevel Λ N ℓ S) (D : FrobeniusVerschiebungData ℓ u.1 Eℓ) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
    FactorsThrough u.2.levK P ↔ mapPt D.F D.F_over P = Eℓ.L.one t

end CerednikDrinfeld.QM.FakeEllipticCurve

end
