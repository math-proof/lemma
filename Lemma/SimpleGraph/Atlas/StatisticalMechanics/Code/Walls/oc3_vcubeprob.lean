import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc3_vcubeprob
open Finset MeasureTheory StatMech.OSSS.GrandCoupling StatMech StatMech.Walls


/--
[oc3_uniformFactor_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubeprob.lean)
-/
@[path]
private lemma oc3_uniformFactor_univ_eq :
-- imply
  (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
-- proof
  apply StatMech.Walls.oc3_uniformFactor_univ

/--
[oc3_uniformFactor_isProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubeprob.lean)
-/
@[path]
private lemma oc3_uniformFactor_isProbabilityMeasure_eq :
-- imply
  IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
-- proof
  apply StatMech.Walls.oc3_uniformFactor_isProbabilityMeasure

/--
[oc3_vcube_eq_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubeprob.lean)
-/
@[path]
private lemma oc3_vcube_eq_pi_eq
  {n : ℕ} :
-- imply
  Vcube n = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
-- proof
  apply StatMech.Walls.oc3_vcube_eq_pi n

/--
[oc3_vcube_univ_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubeprob.lean)
-/
@[path]
private lemma oc3_vcube_univ_prod_eq
  {n : ℕ} :
-- imply
  (Vcube n) Set.univ = ∏ _i : Fin n, (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ := by
-- proof
  apply StatMech.Walls.oc3_vcube_univ_prod n

/--
[oc3_vcube_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubeprob.lean)
-/
@[path]
private lemma oc3_vcube_univ_eq
  {n : ℕ} :
-- imply
  (Vcube n) Set.univ = 1 := by
-- proof
  apply StatMech.Walls.oc3_vcube_univ n

/--
[oc3_vcube_isProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubeprob.lean)
-/
@[path]
private lemma oc3_vcube_isProbabilityMeasure_eq
  {n : ℕ} :
-- imply
  IsProbabilityMeasure (Vcube n) := by
-- proof
  apply StatMech.Walls.oc3_vcube_isProbabilityMeasure n

/--
[oc3_vcube_isProbabilityMeasure_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_vcubeprob.lean)
-/
@[path]
private lemma oc3_vcube_isProbabilityMeasure_consistent_eq
  {n : ℕ} :
-- imply
  (oc3_vcube_isProbabilityMeasure n).measure_univ = (inferInstance : IsProbabilityMeasure (Vcube n)).measure_univ := by
-- proof
  apply StatMech.Walls.oc3_vcube_isProbabilityMeasure_consistent n


-- created on 2026-10-23
