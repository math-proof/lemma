import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc36route
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc36_resummation_lhs_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_resummation_lhs_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {g : V}
  {zero x : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ ∑' m₀ : ↥G.edgeFinset → ℕ, (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V) then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) {zero, x} else 0) := by
-- proof
  apply StatMech.Walls.gc36_resummation_lhs_nonneg G β J hβ hJ S g zero x

/--
[gc36_resummation_sourceless_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_resummation_sourceless_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ ∑' m₀ : ↥G.edgeFinset → ℕ, (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V) then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) ∅ else 0) := by
-- proof
  apply StatMech.Walls.gc36_resummation_sourceless_nonneg G β J hβ hJ S g

/--
[gc36_resummation_rhs_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_resummation_rhs_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {g : V}
  {zero x : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ expectationJ G β (couplingIn J S) {zero, x} * (∑' m₀ : ↥G.edgeFinset → ℕ, (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V) then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) ∅ else 0)) := by
-- proof
  apply StatMech.Walls.gc36_resummation_rhs_nonneg G β J hβ hJ S g zero x

/--
[gc36_resummation_preserves_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_resummation_preserves_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {g : V}
  {zero x : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hg : g ∉ S)
  (h0 : zero ∈ S)
  (hx : x ∈ S)
  (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
-- imply
  (0 ≤ ∑' m₀ : ↥G.edgeFinset → ℕ, (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V) then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) {zero, x} else 0)) ∧ (∑' m₀ : ↥G.edgeFinset → ℕ, (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = ({zero, x} : Finset V) then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) {zero, x} else 0)) = expectationJ G β (couplingIn J S) {zero, x} * (∑' m₀ : ↥G.edgeFinset → ℕ, (if notConnComp G (Sharpness.ofEdgeFun G m₀) g = S ∧ Sharpness.sources G (Sharpness.ofEdgeFun G m₀) = (∅ : Finset V) then hnw_mass G β J (Sharpness.ofEdgeFun G m₀) ∅ else 0)) := by
-- proof
  apply StatMech.Walls.gc36_resummation_preserves_sign G β J hβ hJ S g hg zero x h0 hx hZ

/--
[gc36_delta_native_eq_Z0sq_cov3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_delta_native_eq_Z0sq_cov3_eq
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
  apply StatMech.Walls.gc36_delta_native_eq_Z0sq_cov3 G β h o x y hox hoy hxy

/--
[gc36_ghs_route_forces_rigid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_ghs_route_forces_rigid_eq
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
  apply StatMech.Walls.gc36_ghs_route_forces_rigid G β h o x y hox hoy hxy hres

/--
[gc36_resummation_delivers_cov3_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_resummation_delivers_cov3_nonneg_eq
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
  apply StatMech.Walls.gc36_resummation_delivers_cov3_nonneg G β h hβ hh o x y hox hoy hxy

/--
[gc36_resummation_is_beta_not_h](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_resummation_is_beta_not_h_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov3sym G β h o s(x, y) - eg_ursell3 G β h o x y = ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Walls.gc36_resummation_is_beta_not_h G β h o x y

/--
[gc36_ghs_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_ghs_of_hdom_eq
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
  apply StatMech.Walls.gc36_ghs_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom

/--
[gc36_native_ursell_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_native_ursell_decomp_eq
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
  apply StatMech.Walls.gc36_native_ursell_decomp G β J M hnd A hm hox hoy hxy hcoh

/--
[gc36_resummation_factor_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_resummation_factor_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {zero x : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ expectationJ G β (couplingIn J S) {zero, x} ∧ expectationJ G β (couplingIn J S) {zero, x} ≤ 1 := by
-- proof
  apply StatMech.Walls.gc36_resummation_factor_mem_Icc G β J hβ hJ S zero x

/--
[gc36_h0_beta_route_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_h0_beta_route_consistent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o x y : V} :
-- imply
  eg_ursell3 G β 0 o x y = 0 ∧ cov3sym G β 0 o s(x, y) = ghsBoundSym G β 0 o s(x, y) := by
-- proof
  apply StatMech.Walls.gc36_h0_beta_route_consistent G β o x y

/--
[gc36_degenerate_h_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_degenerate_h_direction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h x x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc36_degenerate_h_direction G β h hβ hh x y hxy

/--
[gc36_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_status_eq
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
  (gc25_nativeAllConnMass G β h o x y = (gc15_Z0 G β h) ^ 2 * cov3sym G β h o s(x, y) ∧ 0 ≤ cov3sym G β h o s(x, y)) ∧ cov3sym G β h o s(x, y) - eg_ursell3 G β h o x y = ghsBoundSym G β h o s(x, y) := by
-- proof
  apply StatMech.Walls.gc36_status G β h hβ hh o x y hox hoy hxy

/--
[gc36_betaSign_does_not_give_hSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_betaSign_does_not_give_hSign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ c b : ℝ, 0 ≤ c ∧ 0 ≤ b ∧ 0 < c - b := by
-- proof
  apply StatMech.Walls.gc36_betaSign_does_not_give_hSign G

/--
[gc36_rigid_relation_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc36route.lean)
-/
@[path]
private lemma gc36_rigid_relation_refuted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∃ Z c b : ℝ, 0 < Z ∧ 0 ≤ c ∧ 0 ≤ b ∧ (Z + 2) * c ≠ Z * b := by
-- proof
  apply StatMech.Walls.gc36_rigid_relation_refuted G


-- created on 2026-10-23
