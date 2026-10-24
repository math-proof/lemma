import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingCriticalShellGreenComparison
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[boundaryEdges_fst_mem_boxSV_vbF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalShellGreenComparison.lean)
-/
@[path]
private lemma boundaryEdges_fst_mem_boxSV_vbF_eq
  {d : Nat}
  {r : Nat}
  {e : Site d × Site d}
-- given
  (hr : 1 <= r)
  (he : e ∈ boundaryEdges d (boxSV_boxF d r)) :
-- imply
  e.1 ∈ boxSV_vbF d r := by
-- proof
  apply StatMech.FrontierA.boundaryEdges_fst_mem_boxSV_vbF hr he

/--
[currentContinuityFreeBoxTwoPoint_shell_le_isingTorus_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalShellGreenComparison.lean)
-/
@[path]
private lemma currentContinuityFreeBoxTwoPoint_shell_le_isingTorus_axis_eq
  {d : Nat}
  {n r k : Nat}
  {beta : Real}
  {x : Site d}
-- given
  (hd : 1 <= d)
  (hr : 1 <= r)
  (hrn : r <= n)
  (hside : 2 * (n + 1) < isingDyadicSide k)
  (hbeta : 0 <= beta)
  (hx : x ∈ boxSV_vbF d r) :
-- imply
  currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) x <= isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift (⟨0, hd⟩ : Fin d) r) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeBoxTwoPoint_shell_le_isingTorus_axis hd hr hrn hside beta hbeta x hx

/--
[currentContinuityFreeTwoPoint_shell_le_latticeGreenBlock_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalShellGreenComparison.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_shell_le_latticeGreenBlock_subcritical_eq
  {d : Nat}
  {beta : Real}
  {r : Nat}
  {x : Site d}
-- given
  (hd : 2 < d)
  (hbeta : 0 < beta)
  (hlt : beta < IsingFK.betaC (magnetization d))
  (hr : 1 <= r)
  (hx : x ∈ boxSV_vbF d r) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) x <= (1 / beta) * isingLatticeGreenAxisBlockAverage (⟨0, by omega⟩ : Fin d) r := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_shell_le_latticeGreenBlock_subcritical hd hbeta hlt r hr x hx

/--
[criticalFreeTwoPoint_shell_le_latticeGreenBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalShellGreenComparison.lean)
-/
@[path]
private lemma criticalFreeTwoPoint_shell_le_latticeGreenBlock_eq
  {d : Nat}
  {r : Nat}
  {x : Site d}
-- given
  (hd : 2 < d)
  (hr : 1 <= r)
  (hx : x ∈ boxSV_vbF d r) :
-- imply
  currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <= (1 / IsingFK.betaC (magnetization d)) * isingLatticeGreenAxisBlockAverage (⟨0, by omega⟩ : Fin d) r := by
-- proof
  apply StatMech.FrontierA.criticalFreeTwoPoint_shell_le_latticeGreenBlock hd r hr x hx

/--
[criticalFreeTwoPoint_uniform_shell_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalShellGreenComparison.lean)
-/
@[path]
private lemma criticalFreeTwoPoint_uniform_shell_decay_eq
  {d : Nat}
  {epsilon : Real}
-- given
  (hd : 2 < d)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ R : Nat, ∀ r : Nat, R <= r -> ∀ x ∈ boxSV_vbF d r, := by
-- proof
  apply StatMech.FrontierA.criticalFreeTwoPoint_uniform_shell_decay hd epsilon hepsilon


-- created on 2026-10-23
