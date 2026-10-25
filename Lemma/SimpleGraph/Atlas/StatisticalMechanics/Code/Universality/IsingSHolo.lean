import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingSHolo.Part7
open StatMech StatMech.Universality StatMech.Universality.IsingMedialVertex


/--
[isingLambda_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingLambda_ne_eq :
-- imply
  isingLambda ≠ 0 := by
-- proof
  apply StatMech.Universality.isingLambda_ne

/--
[isingLambda_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingLambda_sq_eq :
-- imply
  isingLambda ^ 2 = Complex.I := by
-- proof
  apply StatMech.Universality.isingLambda_sq

/--
[isingSqrt2_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingSqrt2_sq_eq :
-- imply
  (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
-- proof
  apply StatMech.Universality.isingSqrt2_sq

/--
[isingSqrt2_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingSqrt2_ne_eq :
-- imply
  (Real.sqrt 2 : ℂ) ≠ 0 := by
-- proof
  apply StatMech.Universality.isingSqrt2_ne

/--
[isingLambda_magic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingLambda_magic_eq :
-- imply
  isingLambda - isingLambda⁻¹ = Complex.I * (Real.sqrt 2 : ℂ) := by
-- proof
  apply StatMech.Universality.isingLambda_magic

/--
[sqrt2_mul_isingLambda](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma sqrt2_mul_isingLambda_eq :
-- imply
  (Real.sqrt 2 : ℂ) * isingLambda = 1 + Complex.I := by
-- proof
  apply StatMech.Universality.sqrt2_mul_isingLambda

/--
[isingLambda_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingLambda_val_eq :
-- imply
  isingLambda = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
-- proof
  apply StatMech.Universality.isingLambda_val

/--
[isingLambda_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingLambda_inv_eq :
-- imply
  isingLambda⁻¹ = (Real.sqrt 2 : ℂ) - isingLambda := by
-- proof
  apply StatMech.Universality.isingLambda_inv

/--
[isingProj_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingProj_add_eq
  {e x y : ℂ} :
-- imply
  isingProj e (x + y) = isingProj e x + isingProj e y := by
-- proof
  apply StatMech.Universality.isingProj_add e x y

/--
[isingProj_of_arg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingProj_of_arg_eq
  {e Fe : ℂ}
-- given
  (he : Complex.normSq e = 1)
  (harg : (starRingEnd ℂ) Fe = e * Fe) :
-- imply
  isingProj e Fe = Fe := by
-- proof
  apply StatMech.Universality.isingProj_of_arg e Fe he harg

/--
[isingF_sHolo_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingF_sHolo_relation_eq
  {X : ℂ} :
-- imply
  isingF 0 X + isingF 1 X = isingF 2 X + isingF 3 X := by
-- proof
  apply StatMech.Universality.isingF_sHolo_relation X

/--
[isingF_case1_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingF_case1_relation_eq :
-- imply
  isingF 0 0 + isingF 1 0 = isingF 2 0 + isingF 3 0 := by
-- proof
  apply StatMech.Universality.isingF_case1_relation

/--
[sHolo_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma sHolo_relation_eq
  {D : IsingMedialVertex} :
-- imply
  D.edgeObs 0 + D.edgeObs 1 = D.edgeObs 2 + D.edgeObs 3 := by
-- proof
  apply StatMech.Universality.IsingMedialVertex.sHolo_relation D

/--
[sHolo_sub_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma sHolo_sub_zero_eq
  {D : IsingMedialVertex} :
-- imply
  D.edgeObs 0 + D.edgeObs 1 - D.edgeObs 2 - D.edgeObs 3 = 0 := by
-- proof
  apply StatMech.Universality.IsingMedialVertex.sHolo_sub_zero D

/--
[contourCombination_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma contourCombination_zero_eq
  {D : IsingMedialVertex} :
-- imply
  D.edgeObs 0 - D.edgeObs 1 + Complex.I * D.edgeObs 3 - Complex.I * D.edgeObs 2 = 0 := by
-- proof
  apply StatMech.Universality.IsingMedialVertex.contourCombination_zero D

/--
[isingContour_expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingContour_expand_eq
  {F : ℂ → ℂ}
  {z : Fin 4 → ℂ} :
-- imply
  isingContour F z = F ((z 0 + z 1) / 2) * (z 1 - z 0) + F ((z 1 + z 2) / 2) * (z 2 - z 1) + F ((z 2 + z 3) / 2) * (z 3 - z 2) + F ((z 3 + z 0) / 2) * (z 0 - z 3) := by
-- proof
  apply StatMech.Universality.isingContour_expand F z

/--
[isingFace_midpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingFace_midpoints_eq
  {v d : ℂ} :
-- imply
  ((isingFace v d 0 + isingFace v d 1) / 2 = v + (1 + Complex.I) / 2 * d) ∧ ((isingFace v d 1 + isingFace v d 2) / 2 = v + (-1 + Complex.I) / 2 * d) ∧ ((isingFace v d 2 + isingFace v d 3) / 2 = v + (-1 - Complex.I) / 2 * d) ∧ ((isingFace v d 3 + isingFace v d 0) / 2 = v + (1 - Complex.I) / 2 * d) := by
-- proof
  apply StatMech.Universality.isingFace_midpoints v d

/--
[isingFace_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingFace_edges_eq
  {v d : ℂ} :
-- imply
  (isingFace v d 1 - isingFace v d 0 = (Complex.I - 1) * d) ∧ (isingFace v d 2 - isingFace v d 1 = (-1 - Complex.I) * d) ∧ (isingFace v d 3 - isingFace v d 2 = (1 - Complex.I) * d) ∧ (isingFace v d 0 - isingFace v d 3 = (1 + Complex.I) * d) := by
-- proof
  apply StatMech.Universality.isingFace_edges v d

/--
[isingContour_eq_combination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma isingContour_eq_combination_eq
  {D : IsingMedialVertex}
  {v d : ℂ}
-- given
  (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 1 + isingFace v d 2) / 2)
  (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
  (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
  (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
  (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
  (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2) :
-- imply
  isingContour (isingObservable D v d) (isingFace v d) = (Complex.I - 1) * d * (D.edgeObs 0 - D.edgeObs 1 + Complex.I * D.edgeObs 3 - Complex.I * D.edgeObs 2) := by
-- proof
  apply StatMech.Universality.isingContour_eq_combination D v d hpq hpr hps hqr hqs hrs

/--
[ising_sholo_face_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma ising_sholo_face_relation_eq
  {D : IsingMedialVertex}
  {v d : ℂ}
-- given
  (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 1 + isingFace v d 2) / 2)
  (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
  (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
  (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
  (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
  (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2) :
-- imply
  isingContour (isingObservable D v d) (isingFace v d) = 0 := by
-- proof
  apply StatMech.Universality.ising_sholo_face_relation D v d hpq hpr hps hqr hqs hrs

/--
[ising_sholo_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean)
-/
@[path]
private lemma ising_sholo_closedContour_eq
  {faces : Finset ι}
  {data : ι → IsingMedialVertex}
  {geo : ι → ℂ × ℂ}
-- given
  (hvanish : ∀ i ∈ faces, isingContour (isingObservable (data i) (geo i).1 (geo i).2) (isingFace (geo i).1 (geo i).2) = 0) :
-- imply
  ∑ i ∈ faces, isingContour (isingObservable (data i) (geo i).1 (geo i).2) (isingFace (geo i).1 (geo i).2) = 0 := by
-- proof
  apply StatMech.Universality.ising_sholo_closedContour faces data geo hvanish


-- created on 2026-10-23
