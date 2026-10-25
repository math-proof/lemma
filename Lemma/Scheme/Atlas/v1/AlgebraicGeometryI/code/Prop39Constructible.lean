import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec21NormalExtension
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec21NormalExtension


namespace Proposition39_g159

/--
[proposition_39_codim2_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop39Constructible.lean)
-/
@[path]
lemma proposition_39_codim2_extension
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [IsIntegrallyClosed A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : Ideal A}
  {x : K}
-- given
  (hI : 2 ≤ I.height)
  (hx : ∀ (p : PrimeSpectrum A), ¬(I ≤ p.asIdeal) → x ∈ Localization.subalgebra.ofField K p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors) :
-- imply
  x ∈ Set.range (algebraMap A K) :=
-- proof
  proposition39_codim2_extension I hI x hx

end Proposition39_g159

namespace Proposition39_g159

/--
[proposition_39_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop39Constructible.lean)
-/
@[path]
lemma proposition_39_range
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [IsIntegrallyClosed A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : Ideal A}
-- given
  (hI : 2 ≤ I.height) :
-- imply
  Set.range (algebraMap A K) = ⋂ (p : PrimeSpectrum A) (_ : ¬(I ≤ p.asIdeal)), (Localization.subalgebra.ofField K p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors : Set K) :=
-- proof
  proposition39_range I hI

end Proposition39_g159


-- created on 2026-10-23
