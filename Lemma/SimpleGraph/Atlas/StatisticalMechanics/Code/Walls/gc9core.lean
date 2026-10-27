import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc9core.Part3
open Finset BigOperators SimpleGraph Set Classical StatMech StatMech.Walls


/--
[gc9_assembledD_pair_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_assembledD_pair_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
  {o g x y : V}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ gc9_assembledD_pair ends F J o g x y := by
-- proof
  apply StatMech.Walls.gc9_assembledD_pair_nonneg G ends F J o g x y hJ hF

/--
[gc9_eq20_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∆ ({some o, none} : Finset (Option V)) = (({x, y} : Finset V).map someEmb) := by
-- proof
  apply StatMech.Walls.gc9_eq20_symmDiff G o x y hox hoy hxy

/--
[gc9_eq20_uv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_uv_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V} :
-- imply
  ({some o, none} : Finset (Option V)) = insert (none : Option V) (({o} : Finset V).map someEmb) := by
-- proof
  apply StatMech.Walls.gc9_eq20_uv G o

/--
[gc9_eq20_card_oxy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_card_oxy_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  Odd (({o, x, y} : Finset V).card) := by
-- proof
  apply StatMech.Walls.gc9_eq20_card_oxy G o x y hox hoy hxy

/--
[gc9_eq20_card_xy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_card_xy_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  Even (({x, y} : Finset V).card) := by
-- proof
  apply StatMech.Walls.gc9_eq20_card_xy G x y hxy

/--
[gc9_cov3_spinProd_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_cov3_spinProd_form_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  cov3sym G β h o s(x, y) = isingExpectation G β h (spinProd ({o, x, y} : Finset V)) - isingExpectation G β h (spinProd ({x, y} : Finset V)) * isingExpectation G β h (spinProd ({o} : Finset V)) := by
-- proof
  apply StatMech.Walls.gc9_cov3_spinProd_form G β h o x y hox hoy hxy

/--
[gc9_eq20_perBond_cov3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_perBond_cov3_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * cov3sym G β h o s(x, y) = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none := by
-- proof
  apply StatMech.Walls.gc9_eq20_perBond_cov3 G β h o x y hox hoy hxy

/--
[gc9_ghostCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_ghostCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
-- given
  (h β : ℝ)
  (hh : 0 ≤ h)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  ∀ e, 0 ≤ ghostCoupling h β J e := by
-- proof
  apply StatMech.Walls.gc9_ghostCoupling_nonneg G h β hh J hJ

/--
[gc9_disconnPivotal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_disconnPivotal_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {A B : Finset (Option V)}
  {u v : Option V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ sourcePairDisconnSum (withGhost G) β (ghostCoupling h β J) A B u v := by
-- proof
  apply StatMech.Walls.gc9_disconnPivotal_nonneg G β h hβ hh J hJ A B u v

/--
[gc9_eq20_pivotalMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_pivotalMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none := by
-- proof
  apply StatMech.Walls.gc9_eq20_pivotalMass_nonneg G β h hβ hh o x y

/--
[gc9_cov3_nonneg_of_eq20](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_cov3_nonneg_of_eq20_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
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
  apply StatMech.Walls.gc9_cov3_nonneg_of_eq20 G β h hβ hh o x y hox hoy hxy

/--
[gc9_deltaEdge_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_deltaEdge_mk_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  gc9_deltaEdge G β h o s(x, y) = sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none := by
-- proof
  apply StatMech.Walls.gc9_deltaEdge_mk G β h o x y

/--
[gc9_eq20_perEdge_cov3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_perEdge_cov3_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {e : Sym2 V}
-- given
  (β h : ℝ)
  (he : e ∈ G.edgeFinset)
  (hoe : o ∉ e) :
-- imply
  gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * cov3sym G β h o e = gc9_deltaEdge G β h o e := by
-- proof
  apply StatMech.Walls.gc9_eq20_perEdge_cov3 G β h o he hoe

/--
[gc9_eq20_pivotalMass_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_pivotalMass_sum_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * (∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), cov3sym G β h o e) = ∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e := by
-- proof
  apply StatMech.Walls.gc9_eq20_pivotalMass_sum G β h o

/--
[gc9_eq20_pivotalMass_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_pivotalMass_sum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ ∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e := by
-- proof
  apply StatMech.Walls.gc9_eq20_pivotalMass_sum_nonneg G β h hβ hh o

/--
[gc9_eq20_derivative_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_derivative_identity_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * deriv (fun β => isingExpectation G β h (fun s => spin s o)) β = gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * (∑ e ∈ G.edgeFinset.filter (fun e => o ∈ e), cov3sym G β h o e) + (∑ e ∈ G.edgeFinset.filter (fun e => o ∉ e), gc9_deltaEdge G β h o e) + gc9_Z_normaliser G β (ghostCoupling h β (fun _ => 1)) * (h * susceptibility G β h o) := by
-- proof
  apply StatMech.Walls.gc9_eq20_derivative_identity G β h o

/--
[gc9_cov3_degenerate_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_cov3_degenerate_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hoy : o ≠ y) :
-- imply
  0 ≤ cov3sym G β h o s(o, y) := by
-- proof
  apply StatMech.Walls.gc9_cov3_degenerate_nonneg G β h hβ hh o y hoy

/--
[gc9_cov3_edge_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_cov3_edge_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {e : Sym2 V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (he : e ∈ G.edgeFinset) :
-- imply
  0 ≤ cov3sym G β h o e := by
-- proof
  apply StatMech.Walls.gc9_cov3_edge_nonneg G β h hβ hh o he

/--
[gc9_cov2_self_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_cov2_self_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ cov2 G β h o o := by
-- proof
  apply StatMech.Walls.gc9_cov2_self_nonneg G β h hβ hh o

/--
[gc9_susceptibility_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_susceptibility_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc9_susceptibility_nonneg G β h hβ hh o

/--
[gc9_beta_deriv_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_beta_deriv_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ deriv (fun β => isingExpectation G β h (fun s => spin s o)) β := by
-- proof
  apply StatMech.Walls.gc9_beta_deriv_nonneg G β h hβ hh o

/--
[gc9_core_ursell_nonpos_of_eq20](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_core_ursell_nonpos_of_eq20_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o g : V}
  {J' : Sym2 (Option V) → ℝ}
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (β h : ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m)
  (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc9_core_ursell_nonpos_of_eq20 G β h o g J' ends F J hJ hF hid x y hox hoy hxy

/--
[gc9_core_signDominance_of_eq20](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_core_signDominance_of_eq20_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o g : V}
  {J' : Sym2 (Option V) → ℝ}
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
-- given
  (β h : ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m)
  (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
-- imply
  GHSSignDominance G β h o := by
-- proof
  apply StatMech.Walls.gc9_core_signDominance_of_eq20 G β h o g J' ends F J hJ hF hid

/--
[gc9_core_ursell_nonpos_all_of_eq20](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_core_ursell_nonpos_all_of_eq20_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o g : V}
  {J' : Sym2 (Option V) → ℝ}
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m)
  (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc9_core_ursell_nonpos_all_of_eq20 G β h hβ hh o g J' ends F J hJ hF hid x y

/--
[gc9_core_ghs_concavity_of_eq20](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_core_ghs_concavity_of_eq20_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o g : V}
  {J' : Sym2 (Option V) → ℝ}
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m)
  (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc9_core_ghs_concavity_of_eq20 G β h hβ hh o g J' ends F J hJ hF hid

/--
[gc9_core_sharpness_of_eq20](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_core_sharpness_of_eq20_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o g : V}
  {Jc : ℝ}
  {J' : Sym2 (Option V) → ℝ}
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m)
  (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ Jc * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc9_core_sharpness_of_eq20 G β h hβ hh o g Jc J' ends F J hJ hF hid hfactor

/--
[gc9_eq20_specific_pins_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_specific_pins_bridge_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o g : V}
  {J' : Sym2 (Option V) → ℝ}
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
-- given
  (β h : ℝ)
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m)
  (hid : gc9_Eq20DerivativeIdentity G β h o g J' ends F J) :
-- imply
  gc8_PivotalSignBridge G β h o := by
-- proof
  apply StatMech.Walls.gc9_eq20_specific_pins_bridge G β h o g J' ends F J hJ hF hid

/--
[gc9_eq20_not_circular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_eq20_not_circular_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u3 Z' D : ℝ}
-- given
  (hZ : 0 < Z')
  (hD : 0 ≤ D)
  (hid : u3 * Z' = -D) :
-- imply
  u3 ≤ 0 := by
-- proof
  apply StatMech.Walls.gc9_eq20_not_circular G hZ hD hid

/--
[gc9_core_normaliser_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_core_normaliser_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 < gc9_Z_normaliser (⊤ : SimpleGraph (Fin 3)) 1 (ghostCoupling 1 1 (fun _ => 1)) := by
-- proof
  apply StatMech.Walls.gc9_core_normaliser_nonvacuous G

/--
[gc9_core_pivotalMass_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean)
-/
@[path]
private lemma gc9_core_pivotalMass_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 ≤ gc9_assembledD_pair (witEnds : Fin 2 → Sym2 (Fin 4)) (fun _ => 1) (fun _ => 1) (0 : Fin 4) 3 1 2 := by
-- proof
  apply StatMech.Walls.gc9_core_pivotalMass_nonvacuous G


-- created on 2026-10-23
