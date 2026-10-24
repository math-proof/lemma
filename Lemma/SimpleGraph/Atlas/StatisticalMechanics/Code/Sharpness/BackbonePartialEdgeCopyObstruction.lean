import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopyObstruction
open StatMech StatMech.Sharpness


/--
[shb_supportLex_literal_domainResummation_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopyObstruction.lean)
-/
@[path]
private lemma shb_supportLex_literal_domainResummation_counterexample_eq :
-- imply
  ¬shb_P3DomainResummation (shbK4Graph shbK4H) (shbK4Graph shbK4G) (shbK4Graph_mono shbK4H_subset_shbK4G) (Real.artanh (2 / 3)) (fun _ => 1) (shbK4DirectPath shbK4H (by decide)) := by
-- proof
  apply StatMech.Sharpness.shb_supportLex_literal_domainResummation_counterexample

/--
[shb_no_universal_supportLex_P3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopyObstruction.lean)
-/
@[path]
private lemma shb_no_universal_supportLex_P3_eq :
-- imply
  ¬(∀ (H G : SimpleGraph (Fin 4)) [DecidableRel H.Adj] [DecidableRel G.Adj] (hHG : H ≤ G) (beta : Real) (J : Sym2 (Fin 4) -> Real) {x y : Fin 4} (p : H.Path x y), shb_rhoSupport G beta J x y (shb_pathMapLe hHG p) ≤ shb_rhoSupport H beta J x y p) := by
-- proof
  apply StatMech.Sharpness.shb_no_universal_supportLex_P3


-- created on 2026-10-23
