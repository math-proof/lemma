import Def.AlgebraicGeometry_FormalGroupAlongSection
import Structure.CerednikDrinfeld_SpecialFormalModule
import Structure.CerednikDrinfeld_QMModuli
import Def.CerednikDrinfeld_QMFormalModuleOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped Quaternion

namespace CerednikDrinfeld.QM

structure IsOrderCoord {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) [Fact q.Prime] (coord : ↥Λ → Zp2 q × Zp2 q) : Prop where
  map_add : ∀ m m' : ↥Λ, coord (m + m') = coord m + coord m'
  map_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, coord ⟨1, h⟩ = (1, 0)
  map_mul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
    coord ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ =
      ((coord m).1 * (coord m').1 + (q : Zp2 q) * ((coord m).2 * WittVector.frobenius (coord m').2),
        (coord m).1 * (coord m').2 + (coord m).2 * WittVector.frobenius (coord m').1)
  injective : Function.Injective coord
  dense : ∀ (k : ℕ) (α β : Zp2 q), ∃ m : ↥Λ,
    (coord m).1 - α ∈ Ideal.span {((q : Zp2 q)) ^ k} ∧ (coord m).2 - β ∈ Ideal.span {((q : Zp2 q)) ^ k}
  trace : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
    (coord m).1 + WittVector.frobenius (coord m).1 = (n : Zp2 q)

end CerednikDrinfeld.QM

end
