module

public import Mathlib
public import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohEquivalenceProof

public section


namespace SerreAffineCriterion

/--
[serre_localization_flat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreAffineCriterion.lean)
-/
public theorem serre_localization_flat
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
