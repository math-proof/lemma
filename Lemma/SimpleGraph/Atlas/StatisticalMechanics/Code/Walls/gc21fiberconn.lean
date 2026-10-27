import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc21fiberconn.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc21_oddFibre_not_of_posFull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean)
-/
@[path]
private lemma gc21_oddFibre_not_of_posFull_eq :
-- imply
  connP (posEdges gc21_E2 gc21_m2) 0 1 ∧ ¬ connP (oddEdges gc21_E2 gc21_m2) 0 1 := by
-- proof
  apply StatMech.Walls.gc21_oddFibre_not_of_posFull

/--
[gc21_posFibre_not_of_posFull_sourceless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean)
-/
@[path]
private lemma gc21_posFibre_not_of_posFull_sourceless_eq :
-- imply
  (∀ e, gc21_k4 e ≤ gc21_m4 e) ∧ Ising.sources gc21_E4 gc21_k4 = (∅ : Finset (Fin 4)) ∧ Ising.sources gc21_E4 gc21_m4 = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ connP (posEdges gc21_E4 gc21_m4) 0 3 ∧ ¬ connP (posEdges gc21_E4 gc21_m4k) 0 3 := by
-- proof
  apply StatMech.Walls.gc21_posFibre_not_of_posFull_sourceless

/--
[gc21_fibre_posTrichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean)
-/
@[path]
private lemma gc21_fibre_posTrichotomy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥(withGhost G).edgeFinset → ℕ}
  {o x y g : Option V}
-- given
  (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) = ({o, x, y, g} : Finset (Option V))) :
-- imply
  connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g ∨ (connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x ∧ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) y g) ∨ (connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y ∧ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) x g) := by
-- proof
  apply StatMech.Walls.gc21_fibre_posTrichotomy G m K₁ o x y g hox hoy hog hxy hxg hyg hbdry

/--
[gc21_fibre_oddArc_of_sourcePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean)
-/
@[path]
private lemma gc21_fibre_oddArc_of_sourcePair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥(withGhost G).edgeFinset → ℕ}
  {u v : Option V}
-- given
  (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
  (huv : u ≠ v)
  (hsrc : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) = {u, v}) :
-- imply
  connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) u v := by
-- proof
  apply StatMech.Walls.gc21_fibre_oddArc_of_sourcePair G m K₁ huv hsrc

/--
[gc21_oddArc_imp_posArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean)
-/
@[path]
private lemma gc21_oddArc_imp_posArc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : ↥(withGhost G).edgeFinset → ℕ}
  {u v : Option V}
-- given
  (hodd : connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n)) u v) :
-- imply
  connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) n)) u v := by
-- proof
  apply StatMech.Walls.gc21_oddArc_imp_posArc G n hodd

/--
[gc21_allConn_oddArcs_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean)
-/
@[path]
private lemma gc21_allConn_oddArcs_of_bridge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥(withGhost G).edgeFinset → ℕ}
  {o x y g : Option V}
-- given
  (hbridge : gc21_FibreOddArcBridge G m)
  (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
  (hposOg : connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g)
  (hposOx : connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x)
  (hposOy : connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y) :
-- imply
  connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o g ∧ connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o x ∧ connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e))) o y := by
-- proof
  apply StatMech.Walls.gc21_allConn_oddArcs_of_bridge G m hbridge K₁ o x y g hposOg hposOx hposOy

/--
[gc21_fibre_starGap_nonpos_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean)
-/
@[path]
private lemma gc21_fibre_starGap_nonpos_of_bridge_eq
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
  (hbridge : gc21_FibreOddArcBridge G m)
  (K₁ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) ∅ - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, none} - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, some x} - hnw_mass (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) (fun e => m e - K₁.1 e)) {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc21_fibre_starGap_nonpos_of_bridge G β h hβ hh o x y m hbridge K₁ hox hoy hxy hbdry

/--
[gc21_firstFour_nonpos_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc21fiberconn.lean)
-/
@[path]
private lemma gc21_firstFour_nonpos_of_bridge_eq
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
  (hbridge : gc21_FibreOddArcBridge G m)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbdry : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc21_firstFour_nonpos_of_bridge G β h hβ hh o x y m hbridge hox hoy hxy hbdry


-- created on 2026-10-23
