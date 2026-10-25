import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivative
open Finset StatMech StatMech.Ising


/--
[scaled_wJ_eq_exp_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma scaled_wJ_eq_exp_interaction_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {s : ConfigSpace V}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (h : V -> Real) :
-- imply
  wJ E (fun e => beta * J e) (fun v => beta * h v) s = Real.exp (beta * inhomogeneousInteraction E J h s) := by
-- proof
  apply StatMech.Ising.scaled_wJ_eq_exp_interaction E J h s beta

/--
[hasDerivAt_scaled_wJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma hasDerivAt_scaled_wJ_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {s : ConfigSpace V}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (h : V -> Real) :
-- imply
  HasDerivAt (fun b => wJ E (fun e => b * J e) (fun v => b * h v) s) (wJ E (fun e => beta * J e) (fun v => beta * h v) s * inhomogeneousInteraction E J h s) beta := by
-- proof
  apply StatMech.Ising.hasDerivAt_scaled_wJ E J h s beta

/--
[hasDerivAt_scaledInhomogeneousPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma hasDerivAt_scaledInhomogeneousPartition_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (h : V -> Real) :
-- imply
  HasDerivAt (scaledInhomogeneousPartition E J h) (∑ s : ConfigSpace V, wJ E (fun e => beta * J e) (fun v => beta * h v) s * inhomogeneousInteraction E J h s) beta := by
-- proof
  apply StatMech.Ising.hasDerivAt_scaledInhomogeneousPartition E J h beta

/--
[hasDerivAt_log_scaledInhomogeneousPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma hasDerivAt_log_scaledInhomogeneousPartition_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (h : V -> Real) :
-- imply
  HasDerivAt (fun b => Real.log (scaledInhomogeneousPartition E J h b)) (scaledMeanInteraction E J h beta) beta := by
-- proof
  apply StatMech.Ising.hasDerivAt_log_scaledInhomogeneousPartition E J h beta

/--
[hasDerivAt_boundaryInterfaceFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma hasDerivAt_boundaryInterfaceFreeEnergy_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real) :
-- imply
  HasDerivAt (boundaryInterfaceFreeEnergy E J hPlus h) (scaledMeanInteraction E J hPlus beta - scaledMeanInteraction E J h beta) beta := by
-- proof
  apply StatMech.Ising.hasDerivAt_boundaryInterfaceFreeEnergy E J hPlus h beta

/--
[expJ_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma expJ_add_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (K : Sym2 V -> Real)
  (h : V -> Real)
  (f g : ConfigSpace V -> Real) :
-- imply
  expJ E K h (fun s => f s + g s) = expJ E K h f + expJ E K h g := by
-- proof
  apply StatMech.Ising.expJ_add E K h f g

/--
[expJ_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma expJ_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {c : Real}
-- given
  (K : Sym2 V -> Real)
  (h : V -> Real)
  (f : ConfigSpace V -> Real) :
-- imply
  expJ E K h (fun s => c * f s) = c * expJ E K h f := by
-- proof
  apply StatMech.Ising.expJ_const_mul E K h c f

/--
[expJ_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma expJ_sum_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {S : Finset I}
-- given
  (K : Sym2 V -> Real)
  (h : V -> Real)
  (f : I -> ConfigSpace V -> Real) :
-- imply
  expJ E K h (fun s => ∑ i ∈ S, f i s) = ∑ i ∈ S, expJ E K h (f i) := by
-- proof
  apply StatMech.Ising.expJ_sum E K h S f

/--
[scaledMeanInteraction_eq_bonds_add_fields](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma scaledMeanInteraction_eq_bonds_add_fields_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (h : V -> Real) :
-- imply
  scaledMeanInteraction E J h beta = (∑ e ∈ E, J e * expJ E (fun a => beta * J a) (fun v => beta * h v) (fun s => bond s e)) + ∑ v : V, h v * expJ E (fun a => beta * J a) (fun x => beta * h x) (fun s => spin s v) := by
-- proof
  apply StatMech.Ising.scaledMeanInteraction_eq_bonds_add_fields E J h beta

/--
[ginibre_boundary_fieldTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma ginibre_boundary_fieldTerm_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
  {x : V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (hbeta : 0 <= beta) :
-- imply
  0 <= hPlus x * expJ E (fun e => beta * J e) (fun v => beta * hPlus v) (fun s => spin s x) - h x * expJ E (fun e => beta * J e) (fun v => beta * h v) (fun s => spin s x) := by
-- proof
  apply StatMech.Ising.ginibre_boundary_fieldTerm_nonneg E J hPlus h hJ hdom beta hbeta x

/--
[boundaryInterfaceFreeEnergy_deriv_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivative.lean)
-/
@[path]
private lemma boundaryInterfaceFreeEnergy_deriv_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (hbeta : 0 <= beta) :
-- imply
  0 <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
-- proof
  apply StatMech.Ising.boundaryInterfaceFreeEnergy_deriv_nonneg E J hPlus h hJ hdom beta hbeta


-- created on 2026-10-23
