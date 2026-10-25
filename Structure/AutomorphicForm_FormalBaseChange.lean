import Mathlib
import Structure.AutomorphicForm_HeckeEigensystem
import Def.AutomorphicForm_FormalBaseChange

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace AutomorphicForm

section FormalLift

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]


end FormalLift


section Package

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

structure JPSSCubicLiftPackage where

  notion : CuspidalityNotion R

  cubicDeg : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S

  lift_automorphic : ∀ π : HeckeEigensystem F R, notion.IsCusp F π →
    ∃ Φ : HeckeEigensystem K R, IsBaseChangeOf π Φ ∧
      (notion.IsCusp K Φ ∨ Φ.IsConstantOnFibers F)

end Package

end AutomorphicForm

end
