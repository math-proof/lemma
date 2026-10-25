import Mathlib
import Structure.ModularCurve_JZeroNeronObjectAtP
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Structure.ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

namespace JZeroNeronObjectAtP

attribute [local instance] instDecidableEqResidueFieldSemistable
  instAlgebraResidueFieldModularFunctionFieldCSemistable

section ShBase

variable (A : ValuationSubring (AlgebraicClosure ℚ))


end ShBase

namespace LevelData

variable {N₀ p : ℕ} [NeZero N₀] {A : ValuationSubring (AlgebraicClosure ℚ)} (Λ : LevelData N₀ p A)


end LevelData

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in


namespace NeronExtension

variable {O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ}

abbrev ptsN (F : O.NeronExtension) (x : JZero (N₀ * p)) : SchemeHomOver (barPt A ≫ shPt A) F.gN :=
  NeronModelInfra.schemeHomOverComp (Λ.shGenLift (O.pts x)) F.openImm

end NeronExtension

end JZeroNeronObjectAtP

end ModularCurve

end
