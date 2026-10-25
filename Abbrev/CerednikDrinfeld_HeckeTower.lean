import Abbrev.AlgebraicCurve_Correspondence
import Lemma.Scheme.IsCurveOver

set_option autoImplicit false

namespace CerednikDrinfeld
namespace HeckeTower

open AlgebraicCurve

abbrev AwayPrime (q q' : ℕ) : Type := {ℓ : Nat.Primes // (ℓ : ℕ) ≠ q ∧ (ℓ : ℕ) ≠ q'}

abbrev Obj (q q' : ℕ) : Type := Option (AwayPrime q q')

abbrev Arr (q q' : ℕ) : Type := AwayPrime q q' × Fin 2

variable {q q' : ℕ}

abbrev dom (α : Arr q q') : Obj q q' := some α.1

abbrev cod (_α : Arr q q') : Obj q q' := none


namespace TowerData

variable {Fbase : Type} [Field Fbase] [Algebra (AlgebraicClosure ℚ) Fbase] (T : TowerData q q' Fbase)


end TowerData

end HeckeTower
end CerednikDrinfeld
