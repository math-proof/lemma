import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[generatedRawMomentTerms_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneRawGenerated.lean)
-/
@[path]
private lemma generatedRawMomentTerms_length_eq :
-- imply
  generatedRawMomentTerms.length = 308 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.generatedRawMomentTerms_length


-- created on 2026-10-23
