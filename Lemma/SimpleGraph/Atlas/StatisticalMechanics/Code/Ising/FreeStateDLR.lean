import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.FreeStateDLR
open MeasureTheory Set StatMech StatMech.Ising


/--
[bondFinsetTouch_subset_bondFinsetInternal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeStateDLR.lean)
-/
@[path]
private lemma bondFinsetTouch_subset_bondFinsetInternal_eq
  {d : Nat}
  {n m : Nat}
-- given
  (hnm : n + 1 <= m) :
-- imply
  bondFinsetTouch d n ⊆ bondFinsetInternal d m := by
-- proof
  apply StatMech.Ising.bondFinsetTouch_subset_bondFinsetInternal hnm

/--
[bond_sum_diff_eq_of_touch_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeStateDLR.lean)
-/
@[path]
private lemma bond_sum_diff_eq_of_touch_subset_eq
  {d : Nat}
  {n m : Nat}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
-- given
  (hnm : n <= m)
  (hsub : bondFinsetTouch d n ⊆ B)
  (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet)
  (sigma : {x // x ∈ box d m} → Bool)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  (∑ e ∈ B, bond (glue eta (ovrBox hnm sigma tau)) e) - (∑ e ∈ B, bond (glue eta sigma) e) = (∑ e ∈ bondFinsetTouch d n, bond (glue eta (ovrBox hnm sigma tau)) e) - (∑ e ∈ bondFinsetTouch d n, bond (glue eta sigma) e) := by
-- proof
  apply StatMech.Ising.bond_sum_diff_eq_of_touch_subset hnm eta B hsub hB sigma tau

/--
[fv_energy_decomp_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeStateDLR.lean)
-/
@[path]
private lemma fv_energy_decomp_outer_eq
  {d : Nat}
  {n m : Nat}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
-- given
  (hnm : n <= m)
  (hsub : bondFinsetTouch d n ⊆ B)
  (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet)
  (h : Real)
  (sigma : {x // x ∈ box d m} → Bool)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy eta m B h sigma + fvEnergy (glue eta sigma) n (bondFinsetTouch d n) h tau = fvEnergy eta m B h (ovrBox hnm sigma tau) + fvEnergy (glue eta (ovrBox hnm sigma tau)) n (bondFinsetTouch d n) h (resBox hnm sigma) := by
-- proof
  apply StatMech.Ising.fv_energy_decomp_outer hnm eta B hsub hB h sigma tau

/--
[fvWeight_spec_symm_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeStateDLR.lean)
-/
@[path]
private lemma fvWeight_spec_symm_outer_eq
  {d : Nat}
  {n m : Nat}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
-- given
  (hnm : n <= m)
  (hsub : bondFinsetTouch d n ⊆ B)
  (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet)
  (beta h : Real)
  (sigma : {x // x ∈ box d m} → Bool)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight eta m B beta h sigma * fvWeight (glue eta sigma) n (bondFinsetTouch d n) beta h tau = fvWeight eta m B beta h (ovrBox hnm sigma tau) * fvWeight (glue eta (ovrBox hnm sigma tau)) n (bondFinsetTouch d n) beta h (resBox hnm sigma) := by
-- proof
  apply StatMech.Ising.fvWeight_spec_symm_outer hnm eta B hsub hB beta h sigma tau

/--
[consistency_double_sum_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeStateDLR.lean)
-/
@[path]
private lemma consistency_double_sum_outer_eq
  {d : Nat}
  {n m : Nat}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
  {g : ConfigSpace (Site d) → Real}
-- given
  (hnm : n <= m)
  (hsub : bondFinsetTouch d n ⊆ B)
  (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet)
  (beta h : Real) :
-- imply
  (∑ sigma : {x // x ∈ box d m} → Bool, fvProb eta m B beta h sigma * ∑ tau : {x // x ∈ box d n} → Bool, fvProb (glue eta sigma) n (bondFinsetTouch d n) beta h tau * g (glue (glue eta sigma) tau)) = ∑ sigma : {x // x ∈ box d m} → Bool, fvProb eta m B beta h sigma * g (glue eta sigma) := by
-- proof
  apply StatMech.Ising.consistency_double_sum_outer hnm eta B hsub hB beta h g

/--
[freeMeasure_specApply_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FreeStateDLR.lean)
-/
@[path]
private lemma freeMeasure_specApply_integral_eq_eq
  {d : Nat}
  {n m : Nat}
  {f : ConfigSpace (Site d) →ᵇ Real}
-- given
  (hnm : n + 1 <= m)
  (beta h : Real) :
-- imply
  (∫ omega, specApply n (bondFinsetTouch d n) beta h (f : ConfigSpace (Site d) → Real) omega ∂(freeMeasure d m beta h : Measure (ConfigSpace (Site d)))) = ∫ omega, f omega ∂(freeMeasure d m beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.freeMeasure_specApply_integral_eq hnm beta h f


-- created on 2026-10-23
