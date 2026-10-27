import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveExtension.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.SLE


/--
[brownianProjectiveContent_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveExtension.lean)
-/
@[path]
private lemma brownianProjectiveContent_tendsto_zero_eq
-- given
  (A : Nat -> Set (Real -> Real))
  (hA : forall n, A n ∈ measurableCylinders fun _ : Real => Real)
  (hanti : Antitone A)
  (hinter : iInter A = ∅) :
-- imply
  Tendsto (fun n => brownianProjectiveContent (A n)) atTop (nhds 0) := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_tendsto_zero A hA hanti hinter

/--
[brownianProjectiveContent_isSigmaSubadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveExtension.lean)
-/
@[path]
private lemma brownianProjectiveContent_isSigmaSubadditive_eq :
-- imply
  brownianProjectiveContent.IsSigmaSubadditive := by
-- proof
  apply StatMech.SLE.brownianProjectiveContent_isSigmaSubadditive

/--
[brownianProductLaw_isProjectiveLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveExtension.lean)
-/
@[path]
private lemma brownianProductLaw_isProjectiveLimit_eq :
-- imply
  IsProjectiveLimit brownianProductLaw brownianFiniteDimensionalPiLaw := by
-- proof
  apply StatMech.SLE.brownianProductLaw_isProjectiveLimit


-- created on 2026-10-23
