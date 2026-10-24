import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc23allconn
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc23_tpsum_firstSlot_switch_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_tpsum_firstSlot_switch_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {A B : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hconn : ∀ K₂ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources G (ofEdgeFun G K₂.1) = B → connP (posEdges G.edgeFinset (ofEdgeFun G (fun e => m e - K₂.1 e))) u v) :
-- imply
  gc15_tpsum G β J m (A ∆ {u, v}) B = gc15_tpsum G β J m A B := by
-- proof
  apply StatMech.Walls.gc23_tpsum_firstSlot_switch_pos G β J m A B huv hconn

/--
[gc23_tpsum_secondSlot_switch_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_tpsum_secondSlot_switch_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {A B : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hconn : ∀ K₁ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources G (ofEdgeFun G K₁.1) = A → connP (posEdges G.edgeFinset (ofEdgeFun G (fun e => m e - K₁.1 e))) u v) :
-- imply
  gc15_tpsum G β J m A (B ∆ {u, v}) = gc15_tpsum G β J m A B := by
-- proof
  apply StatMech.Walls.gc23_tpsum_secondSlot_switch_pos G β J m A B huv hconn

/--
[gc23_tpsum_starPair_collapse_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_tpsum_starPair_collapse_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥G.edgeFinset → ℕ}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hconn : ∀ K₂ : {K : ↥G.edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources G (ofEdgeFun G K₂.1) = ∅ → connP (posEdges G.edgeFinset (ofEdgeFun G (fun e => m e - K₂.1 e))) u v) :
-- imply
  gc15_tpsum G β J m ∅ {u, v} = gc15_tpsum G β J m ∅ ∅ := by
-- proof
  apply StatMech.Walls.gc23_tpsum_starPair_collapse_pos G β J m huv hconn

/--
[gc23_fibre_starGap_nonpos_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_fibre_starGap_nonpos_uncond_eq
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
  (K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅ - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none} - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x} - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc23_fibre_starGap_nonpos_uncond G β h hβ hh o x y m K₂ hox hoy hxy hbdry

/--
[gc23_firstFour_nonpos_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_firstFour_nonpos_uncond_eq
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
  (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc23_firstFour_nonpos_uncond G β h hβ hh o x y hox hoy hxy m hbdry

/--
[gc23_pair_mass_le_base_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_pair_mass_le_base_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {p : ↥(withGhost G).edgeFinset → ℕ}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (huv : (some u : Option V) ≠ some v) :
-- imply
  hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) {some u, some v} ≤ hnw_mass (withGhost G) β J (ofEdgeFun (withGhost G) p) ∅ := by
-- proof
  apply StatMech.Walls.gc23_pair_mass_le_base_pos G β J hβ hJ p huv

/--
[gc23_fifth_le_starless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_fifth_le_starless_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} ≤ gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some x, none} := by
-- proof
  apply StatMech.Walls.gc23_fifth_le_starless G β h hβ hh o x y m

/--
[gc23_allConnResidue_iff_fifthDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_allConnResidue_iff_fifthDomination_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  gc23_fifthDomination G β h o x y ↔ gc22_AllConnResidue G β h o x y := by
-- proof
  apply StatMech.Walls.gc23_allConnResidue_iff_fifthDomination G β h o x y

/--
[gc23_cert_of_fifthDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_cert_of_fifthDomination_eq
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
  (hdom : gc23_fifthDomination G β h o x y) :
-- imply
  gc16_PerConfigCert G β h o x y := by
-- proof
  apply StatMech.Walls.gc23_cert_of_fifthDomination G β h hβ hh o x y hox hoy hxy hdom

/--
[gc23_ursell_nonpos_of_fifthDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_ursell_nonpos_of_fifthDomination_eq
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
  (hdom : gc23_fifthDomination G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc23_ursell_nonpos_of_fifthDomination G β h hβ hh o x y hox hoy hxy hdom

/--
[gc23_deficit_reorg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_deficit_reorg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ = ∑ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, (if sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ then weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) K₂.1) else 0) * (hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, none} + hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some x} + hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) {some o, some y} - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e)) ∅) := by
-- proof
  apply StatMech.Walls.gc23_deficit_reorg G β h o x y m

/--
[gc23_fifthDomination_of_fifthVanish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc23allconn.lean)
-/
@[path]
private lemma gc23_fifthDomination_of_fifthVanish_eq
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
  (hT4 : gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} = 0) :
-- imply
  2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} ≤ gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} + gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ := by
-- proof
  apply StatMech.Walls.gc23_fifthDomination_of_fifthVanish G β h hβ hh o x y hox hoy hxy m hbdry hT4


-- created on 2026-10-23
