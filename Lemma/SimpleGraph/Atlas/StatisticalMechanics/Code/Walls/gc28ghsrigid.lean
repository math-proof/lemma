import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc28ghsrigid
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc28_delta_eq_Z0sq_cov3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc28ghsrigid.lean)
-/
@[path]
private lemma gc28_delta_eq_Z0sq_cov3_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc25_nativeAllConnMass G β h o x y = (gc15_Z0 G β h) ^ 2 * cov3sym G β h o s(x, y) := by
-- proof
  apply StatMech.Walls.gc28_delta_eq_Z0sq_cov3 G β h o x y hox hoy hxy

/--
[gc28_nativeResummation_forces_ursell_proportional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc28ghsrigid.lean)
-/
@[path]
private lemma gc28_nativeResummation_forces_ursell_proportional_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : gc25_NativeResummation G β h o x y) :
-- imply
  gc15_Z0 G β h * eg_ursell3 G β h o x y = -2 * cov3sym G β h o s(x, y) := by
-- proof
  apply StatMech.Walls.gc28_nativeResummation_forces_ursell_proportional G β h o x y hox hoy hxy hres

/--
[gc28_nativeResummation_forces_rigid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc28ghsrigid.lean)
-/
@[path]
private lemma gc28_nativeResummation_forces_rigid_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hres : gc25_NativeResummation G β h o x y) :
-- imply
  (gc15_Z0 G β h + 2) * cov3sym G β h o s(x, y) = gc15_Z0 G β h * ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Walls.gc28_nativeResummation_forces_rigid G β h o x y hox hoy hxy hres

/--
[gc28_native_ursell_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc28ghsrigid.lean)
-/
@[path]
private lemma gc28_native_ursell_decomp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
-- imply
  ∑ m ∈ M, hnw_gap G β J m A o x y = (∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) - 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) := by
-- proof
  apply StatMech.Walls.gc28_native_ursell_decomp G β J M hnd A hm hox hoy hxy hcoh

/--
[gc28_native_closure_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc28ghsrigid.lean)
-/
@[path]
private lemma gc28_native_closure_of_hdom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Sharpness.Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
-- imply
  0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y := by
-- proof
  apply StatMech.Walls.gc28_native_closure_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom

/--
[gc28_proportional_closes_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc28ghsrigid.lean)
-/
@[path]
private lemma gc28_proportional_closes_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hprop : gc15_Z0 G β h * eg_ursell3 G β h o x y = -2 * cov3sym G β h o s(x, y)) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc28_proportional_closes_ghs G β h hβ hh o x y hox hoy hxy hprop

/--
[gc28_cov3_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc28ghsrigid.lean)
-/
@[path]
private lemma gc28_cov3_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  0 ≤ cov3sym G β h o s(x, y) := by
-- proof
  apply StatMech.Walls.gc28_cov3_nonneg G β h hβ hh o x y hox hoy hxy


-- created on 2026-10-23
