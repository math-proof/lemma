import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
open Finset StatMech StatMech.Ising


/--
[interfaceField_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma interfaceField_apply_eq
  {d : ℕ}
  {i : Fin d}
  {x : Site d} :
-- imply
  interfaceField i x = decide (0 ≤ x i) := by
-- proof
  apply StatMech.Ising.interfaceField_apply i x

/--
[fvMeanNegEnergy_eq_sum_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma fvMeanNegEnergy_eq_sum_prob_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (beta h : ℝ) :
-- imply
  fvMeanNegEnergy eta n B beta h = ∑ tau : {x // x ∈ box d n} → Bool, fvProb eta n B beta h tau * (-fvEnergy eta n B h tau) := by
-- proof
  apply StatMech.Ising.fvMeanNegEnergy_eq_sum_prob eta n B beta h

/--
[hasDerivAt_fvWeight_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma hasDerivAt_fvWeight_beta_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (beta h : ℝ)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  HasDerivAt (fun b => fvWeight eta n B b h tau) (fvWeight eta n B beta h tau * (-fvEnergy eta n B h tau)) beta := by
-- proof
  apply StatMech.Ising.hasDerivAt_fvWeight_beta eta n B beta h tau

/--
[hasDerivAt_fvZ_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma hasDerivAt_fvZ_beta_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (beta h : ℝ) :
-- imply
  HasDerivAt (fun b => fvZ eta n B b h) (∑ tau : {x // x ∈ box d n} → Bool, fvWeight eta n B beta h tau * (-fvEnergy eta n B h tau)) beta := by
-- proof
  apply StatMech.Ising.hasDerivAt_fvZ_beta eta n B beta h

/--
[hasDerivAt_log_fvZ_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma hasDerivAt_log_fvZ_beta_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (beta h : ℝ) :
-- imply
  HasDerivAt (fun b => Real.log (fvZ eta n B b h)) (fvMeanNegEnergy eta n B beta h) beta := by
-- proof
  apply StatMech.Ising.hasDerivAt_log_fvZ_beta eta n B beta h

/--
[hasDerivAt_finiteInterfaceFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma hasDerivAt_finiteInterfaceFreeEnergy_eq
  {d : ℕ}
  {i : Fin d}
  {n : ℕ}
  {beta : ℝ} :
-- imply
  HasDerivAt (finiteInterfaceFreeEnergy i n) (fvMeanNegEnergy (plusField d) n (bondFinsetTouch d n) beta 0 - fvMeanNegEnergy (interfaceField i) n (bondFinsetTouch d n) beta 0) beta := by
-- proof
  apply StatMech.Ising.hasDerivAt_finiteInterfaceFreeEnergy i n beta

/--
[finiteInterfaceFreeEnergy_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma finiteInterfaceFreeEnergy_zero_eq
  {d : ℕ}
  {i : Fin d}
  {n : ℕ} :
-- imply
  finiteInterfaceFreeEnergy i n 0 = 0 := by
-- proof
  apply StatMech.Ising.finiteInterfaceFreeEnergy_zero i n

/--
[boundary_free_logFvZ_sub_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma boundary_free_logFvZ_sub_abs_le_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  |Real.log (fvZ eta n (bondFinsetTouch d n) beta h) - Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h)| ≤ |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card := by
-- proof
  apply StatMech.Ising.boundary_free_logFvZ_sub_abs_le eta n beta h

/--
[finiteInterfaceFreeEnergy_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteVolume.lean)
-/
@[path]
private lemma finiteInterfaceFreeEnergy_abs_le_eq
  {d : ℕ}
  {i : Fin d}
  {n : ℕ}
  {beta : ℝ} :
-- imply
  |finiteInterfaceFreeEnergy i n beta| ≤ 2 * |beta| * ((bondFinsetTouch d n) \ (bondFinsetInternal d n)).card := by
-- proof
  apply StatMech.Ising.finiteInterfaceFreeEnergy_abs_le i n beta


-- created on 2026-10-23
