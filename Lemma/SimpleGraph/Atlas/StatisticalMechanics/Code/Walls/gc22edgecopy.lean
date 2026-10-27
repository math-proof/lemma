import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc22edgecopy.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc22_splitWeightedSum_eq_edgecopy_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_splitWeightedSum_eq_edgecopy_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {p : ↥G.edgeFinset → ℕ}
  {A : Finset V} :
-- imply
  splitWeightedSum G β J (ofEdgeFun G p) 1 A = (#((univ : Finset (Finset (Copy G p))).filter (fun S => RandomCurrent.sources (endsM G p) S = A)) : ℝ) * weight G β J (ofEdgeFun G p) := by
-- proof
  apply StatMech.Walls.gc22_splitWeightedSum_eq_edgecopy_count G β J p A

/--
[gc22_count_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_count_collapse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {u v : V}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (huv : u ≠ v)
  (hconn : connK ends (univ : Finset ι) u v) :
-- imply
  #((univ : Finset (Finset ι)).filter (fun K => RandomCurrent.sources ends K = A ∆ {u, v})) = #((univ : Finset (Finset ι)).filter (fun K => RandomCurrent.sources ends K = A)) := by
-- proof
  apply StatMech.Walls.gc22_count_collapse G ends hnd A huv hconn

/--
[gc22_splitWeightedSum_switch_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_splitWeightedSum_switch_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {p : ↥G.edgeFinset → ℕ}
  {A : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hpos : connP (posEdges G.edgeFinset (ofEdgeFun G p)) u v) :
-- imply
  splitWeightedSum G β J (ofEdgeFun G p) 1 (A ∆ {u, v}) = splitWeightedSum G β J (ofEdgeFun G p) 1 A := by
-- proof
  apply StatMech.Walls.gc22_splitWeightedSum_switch_pos G β J p A huv hpos

/--
[gc22_hnw_mass_collapse_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_hnw_mass_collapse_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {p : ↥G.edgeFinset → ℕ}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hpos : connP (posEdges G.edgeFinset (ofEdgeFun G p)) u v) :
-- imply
  hnw_mass G β J (ofEdgeFun G p) {u, v} = hnw_mass G β J (ofEdgeFun G p) ∅ := by
-- proof
  apply StatMech.Walls.gc22_hnw_mass_collapse_pos G β J p huv hpos

/--
[gc22_fibre_starGap_nonpos_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_fibre_starGap_nonpos_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {p : ↥(withGhost G).edgeFinset → ℕ}
  {o x y : V}
  {Hg : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) p)) (some o) none}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (Harc : connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) p)) (some o) (some x) ∨ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) p)) (some o) (some y)) :
-- imply
  hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) ∅ - hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, none} - hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, some x} - hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc22_fibre_starGap_nonpos_pos G β J hβ hJ p hog hoxs hoys Hg Harc

/--
[gc22_fibre_arc_of_disc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_fibre_arc_of_disc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥(withGhost G).edgeFinset → ℕ}
  {o x y : V}
-- given
  (K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) = ({some o, some x, some y, none} : Finset (Option V)))
  (Hg : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) none) :
-- imply
  connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x) ∨ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y) := by
-- proof
  apply StatMech.Walls.gc22_fibre_arc_of_disc G m K₂ hox hoy hxy hbdry Hg

/--
[gc22_firstFour_nonpos_of_fullDisc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_firstFour_nonpos_of_fullDisc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)))
  (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc22_firstFour_nonpos_of_fullDisc G β h hβ hh o x y hox hoy hxy m hbdry hdiscG

/--
[gc22_cert_nonpos_of_fullDisc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_cert_nonpos_of_fullDisc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)))
  (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc22_cert_nonpos_of_fullDisc G β h hβ hh o x y hox hoy hxy m hbdry hdiscG

/--
[gc22_cert_of_allConnResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_cert_of_allConnResidue_eq
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
  (hres : gc22_AllConnResidue G β h o x y) :
-- imply
  gc16_PerConfigCert G β h o x y := by
-- proof
  apply StatMech.Walls.gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy hres

/--
[gc22_ursell_nonpos_of_allConnResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_ursell_nonpos_of_allConnResidue_eq
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
  (hres : gc22_AllConnResidue G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc22_ursell_nonpos_of_allConnResidue G β h hβ hh o x y hox hoy hxy hres

/--
[gc22_ghs_of_allConnResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_ghs_of_allConnResidue_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc22_AllConnResidue G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc22_ghs_of_allConnResidue G β h hβ hh o hres

/--
[gc22_aizenman_barsky_of_allConnResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean)
-/
@[path]
private lemma gc22_aizenman_barsky_of_allConnResidue_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc22_AllConnResidue G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc22_aizenman_barsky_of_allConnResidue G β h hβ hh o J hres hfactor


-- created on 2026-10-23
