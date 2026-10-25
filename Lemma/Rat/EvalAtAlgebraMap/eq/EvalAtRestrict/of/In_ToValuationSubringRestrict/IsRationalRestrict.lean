import Mathlib
import sympy.Basic
import Def.AlgebraicCurve_PlaceEvaluation
import Lemma.AlgebraicCurve.DivisorPushPull
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open IsLocalRing AlgebraicCurve AlgebraicCurve.Place
open Int


/--
[AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
  {w : Place K F'}
  {g : F}
-- given
  (hv : (w.restrict F).IsRational)
  (hg : g ∈ (w.restrict F).toValuationSubring) :
-- imply
  w.evalAt (algebraMap F F' g) = (w.restrict F).evalAt g := by
  have hg' : algebraMap F F' g ∈ w.toValuationSubring := ValuationSubring.mem_comap.mp hg
  have h2 : residue w.toValuationSubring (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring) = algebraMap K w.ResidueField ((w.restrict F).evalAt g) := by
-- proof
    have h3 : (⟨algebraMap F F' g, hg'⟩ : w.toValuationSubring) = restrictInclusion F w ⟨g, hg⟩ := rfl
    rw [h3, ← restrictResidueMap_residue, ((w.restrict F).algebraMap_evalAt hv hg).symm]
    show restrictResidueMap F w
      (residue _ (algebraMap K (w.restrict F).toValuationSubring ((w.restrict F).evalAt g))) = residue _ (algebraMap K w.toValuationSubring ((w.restrict F).evalAt g))
    rw [restrictResidueMap_residue]
    refine congrArg _ (Subtype.ext ?_)
    show algebraMap F F' (algebraMap K F ((w.restrict F).evalAt g)) = algebraMap K F' ((w.restrict F).evalAt g)
    rw [← IsScalarTower.algebraMap_apply]
  rw [w.evalAt_of_mem hg', h2, w.residueInv_algebraMap]


-- created on 2026-10-24
