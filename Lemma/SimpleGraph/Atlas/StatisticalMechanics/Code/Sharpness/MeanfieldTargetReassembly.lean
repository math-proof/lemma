import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldTargetReassembly.Part2
open Finset Set SimpleGraph StatMech StatMech.Sharpness


/--
[mtr_probV_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean)
-/
@[path]
private lemma mtr_probV_compl_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {A : Set (ConfigSpace (Sym2 W))}
-- given
  (p : Sym2 W -> Real) :
-- imply
  probV p Aᶜ = 1 - probV p A := by
-- proof
  apply StatMech.Sharpness.mtr_probV_compl H p A

/--
[mtr_crossing_compl_eq_sum_surfaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean)
-/
@[path]
private lemma mtr_crossing_compl_eq_sum_surfaces_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {o : W}
  {B : Set W}
-- given
  (p : Sym2 W -> Real) :
-- imply
  1 - probV p (mpiCrossingEvent H o B) = ∑ S ∈ (Finset.univ.filter fun S : Finset W => o ∈ S), probV p (mpiSurfaceEvent H B S) := by
-- proof
  apply StatMech.Sharpness.mtr_crossing_compl_eq_sum_surfaces H p o B

/--
[mtr_probV_eq_sum_inter_surfaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean)
-/
@[path]
private lemma mtr_probV_eq_sum_inter_surfaces_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {o : W}
  {B : Set W}
  {C : Set (ConfigSpace (Sym2 W))}
-- given
  (p : Sym2 W -> Real)
  (hC : C ⊆ (mpiCrossingEvent H o B)ᶜ) :
-- imply
  probV p C = ∑ S ∈ (Finset.univ.filter fun S : Finset W => o ∈ S), probV p (C ∩ mpiSurfaceEvent H B S) := by
-- proof
  apply StatMech.Sharpness.mtr_probV_eq_sum_inter_surfaces H p o B C hC

/--
[mtr_surface_phi_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean)
-/
@[path]
private lemma mtr_surface_phi_factor_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {D : Finset (Sym2 W)}
  {o : W}
  {B : Set W}
  {S : Finset W}
-- given
  (p : Sym2 W -> Real) :
-- imply
  mtrPhi H p D o S * probV p (mpiSurfaceEvent H B S) = ∑ q ∈ shk_boundaryPairs H S, if s(q.1, q.2) ∈ D then p s(q.1, q.2) * probV p (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S) else 0 := by
-- proof
  apply StatMech.Sharpness.mtr_surface_phi_factor H p D o B S

/--
[mtr_boundary_le_closedPivotal_surface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean)
-/
@[path]
private lemma mtr_boundary_le_closedPivotal_surface_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {D : Finset (Sym2 W)}
  {beta : Real}
  {o : W}
  {B : Set W}
  {S : Finset W}
-- given
  (p c : Sym2 W -> Real)
  (hp : ∀ e, 0 <= p e ∧ p e <= 1)
  (hbeta : 0 <= beta)
  (hc : ∀ e ∈ D, 0 <= c e)
  (hpc : ∀ e ∈ D, p e <= beta * c e)
  (ho : o ∈ S) :
-- imply
  (∑ q ∈ shk_boundaryPairs H S, if s(q.1, q.2) ∈ D then p s(q.1, q.2) * probV p (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S) else 0) <= beta * ∑ e ∈ D, c e * probV p (abgiClosedPivotal e (mpiCrossingEvent H o B) ∩ mpiSurfaceEvent H B S) := by
-- proof
  apply StatMech.Sharpness.mtr_boundary_le_closedPivotal_surface H p c hp D beta hbeta hc hpc o B S ho

/--
[mtr_meanfield_reassembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldTargetReassembly.lean)
-/
@[path]
private lemma mtr_meanfield_reassembly_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {D : Finset (Sym2 W)}
  {beta m : Real}
  {o : W}
  {B : Set W}
-- given
  (p c : Sym2 W -> Real)
  (hp : ∀ e, 0 <= p e ∧ p e <= 1)
  (hbeta : 0 <= beta)
  (hc : ∀ e ∈ D, 0 <= c e)
  (hpc : ∀ e ∈ D, p e <= beta * c e)
  (hm : ∀ S : Finset W, o ∈ S -> (mpiSurfaceEvent H B S).Nonempty -> m <= mtrPhi H p D o S) :
-- imply
  m * (1 - probV p (mpiCrossingEvent H o B)) <= beta * ∑ e ∈ D, c e * probV p (abgiClosedPivotal e (mpiCrossingEvent H o B)) := by
-- proof
  apply StatMech.Sharpness.mtr_meanfield_reassembly H p c hp D beta m hbeta hc hpc o B hm


-- created on 2026-10-23
