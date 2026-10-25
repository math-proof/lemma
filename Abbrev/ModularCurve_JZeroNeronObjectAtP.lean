import Mathlib
import Structure.ModularCurve_JZeroNeronIdentityComponent
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
import Def.ModularCurve_ReductionOfPointsAgreesModL
import Instance.ModularCurve_JZeroSemistableSpecialization
import Structure.ModularCurve_JZeroNeronData
import Structure.ModularCurve_ToricDescentData
import Def.GaloisRep_Flat
import Def.FLTPrelim_Ramification
import Lemma.ModularCurve.SupersingularNodePlaces
import Structure.JacJ1Iface
import Structure.ModularCurve_JZeroNeronObjectAtP

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

namespace JZeroNeronObjectAtP


abbrev muToTorus (S : Type) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i))))


abbrev muBaseChange {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (t m : ℕ) :
    muScheme S' t m ⟶ muScheme S t m :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) φ))


namespace LevelData

variable {N₀ p : ℕ} [NeZero N₀] {A : ValuationSubring (AlgebraicClosure ℚ)}

end LevelData

end JZeroNeronObjectAtP

open JZeroNeronObjectAtP

attribute [local instance] instDecidableEqResidueFieldSemistable
  instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in


namespace JZeroNeronObjectAtP

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : LevelData N₀ p A}

abbrev nodes (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) ×
      Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀)) :=
  nodePairsOfPlaces O.frob O.ssFinset

end JZeroNeronObjectAtP

end ModularCurve

end
