import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohEquivalenceProof


namespace SerreAffineCriterion

/--
[serre_localization_flat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreAffineCriterion.lean)
-/
@[path]
lemma serre_localization_flat
  {R : Type*}
  [CommRing R]
  {S : Submonoid R} :
-- imply
  Module.Flat R (Localization S) :=
-- proof
  IsLocalization.flat _ S
end LocalizationExact
section GammaExact
end GammaExact

end SerreAffineCriterion


-- created on 2026-10-23
