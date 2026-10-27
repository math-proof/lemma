import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc11core.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc11_Z0_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_Z0_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  0 < gc11_Z0 G β h := by
-- proof
  apply StatMech.Walls.gc11_Z0_pos G β h

/--
[gc11_cleared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_cleared_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  eg_ursell4_ghostPlus G β h o x y * (gc11_Z0 G β h) ^ 2 = gc11_Z0 G β h * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h) (({o, x} : Finset V).map someEmb) (insert (none : Option V) (({y} : Finset V).map someEmb)) - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h) (({o, y} : Finset V).map someEmb) (insert (none : Option V) (({x} : Finset V).map someEmb)) - Sharpness.sourcePairSum (withGhost G) β (gc11_Jghost β h) (insert (none : Option V) (({o} : Finset V).map someEmb)) (({x, y} : Finset V).map someEmb) := by
-- proof
  apply StatMech.Walls.gc11_cleared G β h o x y

/--
[gc11_triple_Z0cube_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_triple_Z0cube_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  (onePt G β h o * onePt G β h x * onePt G β h y) * (gc11_Z0 G β h) ^ 3 = Sharpness.currentSum (withGhost G) β (gc11_Jghost β h) (insert (none : Option V) (({o} : Finset V).map someEmb)) * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h) (insert (none : Option V) (({x} : Finset V).map someEmb)) * Sharpness.currentSum (withGhost G) β (gc11_Jghost β h) (insert (none : Option V) (({y} : Finset V).map someEmb)) := by
-- proof
  apply StatMech.Walls.gc11_triple_Z0cube_eq G β h o x y

/--
[gc11_clearedSign_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_clearedSign_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  gc11_ClearedSign G β h o ↔ gc10_GhostFourPointSign G β h o := by
-- proof
  apply StatMech.Walls.gc11_clearedSign_iff G β h o

/--
[gc11_ghostFourPointSign_of_clearedSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_ghostFourPointSign_of_clearedSign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hres : gc11_ClearedSign G β h o) :
-- imply
  gc10_GhostFourPointSign G β h o := by
-- proof
  apply StatMech.Walls.gc11_ghostFourPointSign_of_clearedSign G β h o hres

/--
[gc11_core_ursell_nonpos_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_core_ursell_nonpos_distinct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hres : gc11_ClearedSign G β h o)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc11_core_ursell_nonpos_distinct G β h o hres hox hoy hxy

/--
[gc11_core_signDominance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_core_signDominance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hres : gc11_ClearedSign G β h o) :
-- imply
  GHSSignDominance G β h o := by
-- proof
  apply StatMech.Walls.gc11_core_signDominance G β h o hres

/--
[gc11_core_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_core_ghs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hres : gc11_ClearedSign G β h o) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc11_core_ghs G β h hβ hh o hres

/--
[gc11_core_sharpness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_core_sharpness_eq
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
  (hres : gc11_ClearedSign G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc11_core_sharpness G β h hβ hh o J hres hfactor

/--
[gc11_clearedSign_of_familyRealise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_clearedSign_of_familyRealise_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hfr : gc5_FamilyRealise G β h o) :
-- imply
  gc11_ClearedSign G β h o := by
-- proof
  apply StatMech.Walls.gc11_clearedSign_of_familyRealise G β h o hfr

/--
[gc11_clearedSign_of_eqSwi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_clearedSign_of_eqSwi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  gc11_ClearedSign G β h o := by
-- proof
  apply StatMech.Walls.gc11_clearedSign_of_eqSwi G β h o hid

/--
[gc11_claim1_griffiths_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_claim1_griffiths_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {eS cS eΛ : ℝ}
-- given
  (hSnn : 0 ≤ eS)
  (hcSnn : 0 ≤ cS)
  (hgriff : eS ≤ eΛ) :
-- imply
  eΛ * (eS * cS) ≥ eS ^ 2 * cS := by
-- proof
  apply StatMech.Walls.gc11_claim1_griffiths_step G eS cS eΛ hSnn hcSnn hgriff

/--
[gc11_cleared_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_cleared_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  eg_ursell4_ghostPlus (⊤ : SimpleGraph (Fin 3)) 1 1 0 1 2 * (gc11_Z0 (⊤ : SimpleGraph (Fin 3)) 1 1) ^ 2 = gc11_Z0 (⊤ : SimpleGraph (Fin 3)) 1 1 * Sharpness.currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (gc11_Jghost 1 1) (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)) - Sharpness.sourcePairSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (gc11_Jghost 1 1) (({0, 1} : Finset (Fin 3)).map someEmb) (insert (none : Option (Fin 3)) (({2} : Finset (Fin 3)).map someEmb)) - Sharpness.sourcePairSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (gc11_Jghost 1 1) (({0, 2} : Finset (Fin 3)).map someEmb) (insert (none : Option (Fin 3)) (({1} : Finset (Fin 3)).map someEmb)) - Sharpness.sourcePairSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (gc11_Jghost 1 1) (insert (none : Option (Fin 3)) (({0} : Finset (Fin 3)).map someEmb)) (({1, 2} : Finset (Fin 3)).map someEmb) := by
-- proof
  apply StatMech.Walls.gc11_cleared_nonvacuous G

/--
[gc11_clearedSign_reduction_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc11core.lean)
-/
@[path]
private lemma gc11_clearedSign_reduction_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  0 < gc11_Z0 (⊤ : SimpleGraph (Fin 3)) 1 1 ∧ (gc11_ClearedSign (⊤ : SimpleGraph (Fin 3)) 1 1 0 ↔ gc10_GhostFourPointSign (⊤ : SimpleGraph (Fin 3)) 1 1 0) := by
-- proof
  apply StatMech.Walls.gc11_clearedSign_reduction_nonvacuous G


-- created on 2026-10-23
