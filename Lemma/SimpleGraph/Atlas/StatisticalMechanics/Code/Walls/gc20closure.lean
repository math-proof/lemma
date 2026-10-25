import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc20closure.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc20_withGhost_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_withGhost_loopless_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ∀ e ∈ (withGhost G).edgeFinset, ¬ e.IsDiag := by
-- proof
  apply StatMech.Walls.gc20_withGhost_loopless G

/--
[gc20_ofEdgeFun_fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_ofEdgeFun_fiber_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥(withGhost G).edgeFinset → ℕ}
  {e : Sym2 (Option V)}
-- given
  (K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}) :
-- imply
  ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e) e ≤ ofEdgeFun (withGhost G) m e := by
-- proof
  apply StatMech.Walls.gc20_ofEdgeFun_fiber_le G m K₂ e

/--
[gc20_fiber_disc_of_disc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_fiber_disc_of_disc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥(withGhost G).edgeFinset → ℕ}
  {u v : Option V}
-- given
  (K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e})
  (hdisc : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) u v) :
-- imply
  ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) u v := by
-- proof
  apply StatMech.Walls.gc20_fiber_disc_of_disc G m K₂ hdisc

/--
[gc20_adjP_posEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_adjP_posEdges_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {a b : V} :
-- imply
  adjP (posEdges G.edgeFinset (ofEdgeFun G m)) a b ↔ (currentSubgraph G (ofEdgeFun G m)).Adj a b := by
-- proof
  apply StatMech.Walls.gc20_adjP_posEdges_iff G m a b

/--
[gc20_connP_posEdges_iff_currentConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_connP_posEdges_iff_currentConnected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {u v : V} :
-- imply
  connP (posEdges G.edgeFinset (ofEdgeFun G m)) u v ↔ CurrentConnected G (ofEdgeFun G m) u v := by
-- proof
  apply StatMech.Walls.gc20_connP_posEdges_iff_currentConnected G m u v

/--
[gc20_disc_iff_connK_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_disc_iff_connK_univ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {u v : V} :
-- imply
  ¬ connP (posEdges G.edgeFinset (ofEdgeFun G m)) u v ↔ ¬ RandomCurrent.connK (FluxEdgeCopy.endsM G m) univ u v := by
-- proof
  apply StatMech.Walls.gc20_disc_iff_connK_univ G m u v

/--
[gc20_fifth_vanish_of_disc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_fifth_vanish_of_disc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hog : (some o : Option V) ≠ none)
  (hdisc : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} = 0 := by
-- proof
  apply StatMech.Walls.gc20_fifth_vanish_of_disc G β h o x y hog m hdisc

/--
[gc20_starGap_zero_pairing1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_starGap_zero_pairing1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {m' : Ising.Current (Option V)}
  {o x y : V}
  {Hox : connP (oddEdges (withGhost G).edgeFinset m') (some o) (some x)}
  {Hg : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) none}
  {Hy : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) (some y)}
-- given
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y) :
-- imply
  hnw_mass (withGhost G) β J m' ∅ - hnw_mass (withGhost G) β J m' {some o, none} - hnw_mass (withGhost G) β J m' {some o, some x} - hnw_mass (withGhost G) β J m' {some o, some y} = 0 := by
-- proof
  apply StatMech.Walls.gc20_starGap_zero_pairing1 G β J m' hog hoxs hoys Hox Hg Hy

/--
[gc20_starGap_zero_pairing2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_starGap_zero_pairing2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {m' : Ising.Current (Option V)}
  {o x y : V}
  {Hoy : connP (oddEdges (withGhost G).edgeFinset m') (some o) (some y)}
  {Hg : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) none}
  {Hx : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) (some x)}
-- given
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y) :
-- imply
  hnw_mass (withGhost G) β J m' ∅ - hnw_mass (withGhost G) β J m' {some o, none} - hnw_mass (withGhost G) β J m' {some o, some x} - hnw_mass (withGhost G) β J m' {some o, some y} = 0 := by
-- proof
  apply StatMech.Walls.gc20_starGap_zero_pairing2 G β J m' hog hoxs hoys Hoy Hg Hx

/--
[gc20_starGap_nonpos_of_disc_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_starGap_nonpos_of_disc_arc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 (Option V) → ℝ}
  {m' : Ising.Current (Option V)}
  {o x y : V}
  {Hg : ¬ connP (posEdges (withGhost G).edgeFinset m') (some o) none}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (Harc : connP (oddEdges (withGhost G).edgeFinset m') (some o) (some x) ∨ connP (oddEdges (withGhost G).edgeFinset m') (some o) (some y)) :
-- imply
  hnw_mass (withGhost G) β J m' ∅ - hnw_mass (withGhost G) β J m' {some o, none} - hnw_mass (withGhost G) β J m' {some o, some x} - hnw_mass (withGhost G) β J m' {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc20_starGap_nonpos_of_disc_arc G β J hβ hJ m' hog hoxs hoys Hg Harc

/--
[gc20_firstFour_zero_pairing1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_firstFour_zero_pairing1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none)
  (hdiscY : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) (some y))
  (hOx : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} = 0 := by
-- proof
  apply StatMech.Walls.gc20_firstFour_zero_pairing1 G β h o x y hog hoxs hoys m hdiscG hdiscY hOx

/--
[gc20_firstFour_zero_pairing2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_firstFour_zero_pairing2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none)
  (hdiscX : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) (some x))
  (hOy : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} = 0 := by
-- proof
  apply StatMech.Walls.gc20_firstFour_zero_pairing2 G β h o x y hog hoxs hoys m hdiscG hdiscX hOy

/--
[gc20_firstFour_nonpos_of_disc_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_firstFour_nonpos_of_disc_arc_eq
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
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none)
  (hArc : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x) ∨ connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc20_firstFour_nonpos_of_disc_arc G β h hβ hh o x y hog hoxs hoys m hdiscG hArc

/--
[gc20_cert_zero_of_pairing1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_cert_zero_of_pairing1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none)
  (hdiscY : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) (some y))
  (hOx : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x)) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} = 0 := by
-- proof
  apply StatMech.Walls.gc20_cert_zero_of_pairing1 G β h o x y hog hoxs hoys m hdiscG hdiscY hOx

/--
[gc20_cert_zero_of_pairing2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_cert_zero_of_pairing2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none)
  (hdiscX : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) (some x))
  (hOy : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} = 0 := by
-- proof
  apply StatMech.Walls.gc20_cert_zero_of_pairing2 G β h o x y hog hoxs hoys m hdiscG hdiscX hOy

/--
[gc20_cert_nonpos_of_disc_arc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_cert_nonpos_of_disc_arc_eq
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
  (hog : (some o : Option V) ≠ none)
  (hoxs : (some o : Option V) ≠ some x)
  (hoys : (some o : Option V) ≠ some y)
  (hdiscG : ¬ connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none)
  (hArc : ∀ K₂ : {K : ↥(withGhost G).edgeFinset → ℕ // ∀ e, K e ≤ m e}, sources (withGhost G) (ofEdgeFun (withGhost G) K₂.1) = ∅ → connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some x) ∨ connP (oddEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) (fun e => m e - K₂.1 e))) (some o) (some y)) :
-- imply
  gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ ∅ - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, none} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some x} - gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m ∅ {some o, some y} + 2 * gc15_tpsum (withGhost G) β (ghostCoupling h β (fun _ => 1)) m {some o, none} {some x, none} ≤ 0 := by
-- proof
  apply StatMech.Walls.gc20_cert_nonpos_of_disc_arc G β h hβ hh o x y hog hoxs hoys m hdiscG hArc

/--
[gc20_cert_of_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_cert_of_trichotomy_eq
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
  (hreg : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc20_FiberConnRegime G β h o x y m) :
-- imply
  gc16_PerConfigCert G β h o x y := by
-- proof
  apply StatMech.Walls.gc20_cert_of_trichotomy G β h o x y hox hoy hxy hreg

/--
[gc20_ursell_nonpos_of_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_ursell_nonpos_of_trichotomy_eq
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
  (hreg : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc20_FiberConnRegime G β h o x y m) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc20_ursell_nonpos_of_trichotomy G β h o x y hox hoy hxy hreg

/--
[gc20_ghs_of_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_ghs_of_trichotomy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hreg : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc20_FiberConnRegime G β h o x y m) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc20_ghs_of_trichotomy G β h hβ hh o hreg

/--
[gc20_aizenman_barsky_of_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean)
-/
@[path]
private lemma gc20_aizenman_barsky_of_trichotomy_eq
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
  (hreg : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc20_FiberConnRegime G β h o x y m)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc20_aizenman_barsky_of_trichotomy G β h hβ hh o J hreg hfactor


-- created on 2026-10-23
