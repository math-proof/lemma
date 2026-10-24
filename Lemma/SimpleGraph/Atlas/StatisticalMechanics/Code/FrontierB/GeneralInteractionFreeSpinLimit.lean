import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.GeneralInteractionFreeSpinLimit
open Filter Topology Set Finset StatMech StatMech.FrontierB


/--
[interactionBoxPredEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean)
-/
@[path]
private lemma interactionBoxPredEquiv_val_eq
  {d : Nat}
  {n m : Nat}
  {x : interactionBoxVertices d n}
-- given
  (hnm : n ≤ m) :
-- imply
  (interactionBoxPredEquiv d hnm x).1.1 = x.1 := by
-- proof
  apply StatMech.FrontierB.interactionBoxPredEquiv_val d hnm x

/--
[generalInteractionBox_spinProd_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean)
-/
@[path]
private lemma generalInteractionBox_spinProd_mono_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {n m : Nat}
  {A : Finset (interactionBoxVertices d n)}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 ≤ beta)
  (hnm : n ≤ m) :
-- imply
  expJ (interactionBoxGraph d n).edgeFinset (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0) (spinProd A) ≤ expJ (interactionBoxGraph d m).edgeFinset (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0) (spinProd (A.map (interactionBoxVertexIncl d hnm))) := by
-- proof
  apply StatMech.FrontierB.generalInteractionBox_spinProd_mono J hJ beta hbeta hnm A

/--
[interactionBoxSpinSupport_map_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean)
-/
@[path]
private lemma interactionBoxSpinSupport_map_inclusion_eq
  {d : Nat}
  {n m : Nat}
  {A : Finset (Site d)}
-- given
  (hnm : n ≤ m)
  (hA : (A : Set (Site d)) ⊆ box d n) :
-- imply
  (interactionBoxSpinSupport d n A).map (interactionBoxVertexIncl d hnm) = interactionBoxSpinSupport d m A := by
-- proof
  apply StatMech.FrontierB.interactionBoxSpinSupport_map_inclusion d hnm A hA

/--
[expJ_spinProd_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean)
-/
@[path]
private lemma expJ_spinProd_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {K : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hf : V → ℝ) :
-- imply
  expJ E K hf (spinProd A) ≤ 1 := by
-- proof
  apply StatMech.FrontierB.expJ_spinProd_le_one E K hf A

/--
[generalInteractionBox_fixed_spinProd_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean)
-/
@[path]
private lemma generalInteractionBox_fixed_spinProd_mono_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {n m : Nat}
  {A : Finset (Site d)}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 ≤ beta)
  (hnm : n ≤ m)
  (hA : (A : Set (Site d)) ⊆ box d n) :
-- imply
  expJ (interactionBoxGraph d n).edgeFinset (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0) (spinProd (interactionBoxSpinSupport d n A)) ≤ expJ (interactionBoxGraph d m).edgeFinset (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0) (spinProd (interactionBoxSpinSupport d m A)) := by
-- proof
  apply StatMech.FrontierB.generalInteractionBox_fixed_spinProd_mono J hJ beta hbeta hnm A hA

/--
[generalInteractionBox_spinProd_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean)
-/
@[path]
private lemma generalInteractionBox_spinProd_tendsto_eq
  {d : Nat}
  {J : Sym2 (Site d) → ℝ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hbeta : 0 ≤ beta) :
-- imply
  ∃ L : ℝ, Tendsto (fun n => expJ (interactionBoxGraph d n).edgeFinset (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0) (spinProd (interactionBoxSpinSupport d n A))) atTop (nhds L) := by
-- proof
  apply StatMech.FrontierB.generalInteractionBox_spinProd_tendsto J hJ beta hbeta A


-- created on 2026-10-23
