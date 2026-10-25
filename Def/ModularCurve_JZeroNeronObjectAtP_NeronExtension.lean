import Mathlib
import Def.ModularCurve_JZeroNeronObjectAtP
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Structure.ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Abbrev.ModularCurve_JZeroNeronObjectAtP_NeronExtension

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


theorem coe_shToPlace (x : ↥(shRing A)) :
    ((shToPlace A x : ↥A) : AlgebraicClosure ℚ) = ((x : ↥(invField A)) : AlgebraicClosure ℚ) := rfl


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

def ExtN (F : O.NeronExtension) (x : JZero (N₀ * p)) : Prop :=
  ∃ s : SchemeHomOver (shPt A) F.gN, (F.ptsN x).1 = barPt A ≫ s.1

def finPts (F : O.NeronExtension) (m : ℕ) : AddSubgroup (JZero (N₀ * p)) :=
  AddSubgroup.closure {x | x ∈ jZeroTorsion (N₀ * p) m ∧ F.ExtN x}

end NeronExtension

end JZeroNeronObjectAtP

end ModularCurve

end
