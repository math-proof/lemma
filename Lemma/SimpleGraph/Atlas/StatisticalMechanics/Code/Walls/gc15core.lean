import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc15_sd0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_sd0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq W]
  {O X Y g : W} :
-- imply
  (∅ : Finset W) ∆ (∅ : Finset W) ∆ {O, X, Y, g} = {O, X, Y, g} := by
-- proof
  apply StatMech.Walls.gc15_sd0 G O X Y g

/--
[gc15_sd1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_sd1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq W]
  {O X Y g : W}
-- given
  (hOX : O ≠ X)
  (hOY : O ≠ Y)
  (hOg : O ≠ g)
  (hXY : X ≠ Y)
  (hXg : X ≠ g)
  (hYg : Y ≠ g) :
-- imply
  (∅ : Finset W) ∆ {O, g} ∆ {X, Y} = {O, X, Y, g} := by
-- proof
  apply StatMech.Walls.gc15_sd1 G O X Y g hOX hOY hOg hXY hXg hYg

/--
[gc15_sd2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_sd2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq W]
  {O X Y g : W}
-- given
  (hOX : O ≠ X)
  (hOY : O ≠ Y)
  (hOg : O ≠ g)
  (hXY : X ≠ Y)
  (hXg : X ≠ g)
  (hYg : Y ≠ g) :
-- imply
  (∅ : Finset W) ∆ {O, X} ∆ {Y, g} = {O, X, Y, g} := by
-- proof
  apply StatMech.Walls.gc15_sd2 G O X Y g hOX hOY hOg hXY hXg hYg

/--
[gc15_sd3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_sd3_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq W]
  {O X Y g : W}
-- given
  (hOX : O ≠ X)
  (hOY : O ≠ Y)
  (hOg : O ≠ g)
  (hXY : X ≠ Y)
  (hXg : X ≠ g)
  (hYg : Y ≠ g) :
-- imply
  (∅ : Finset W) ∆ {O, Y} ∆ {X, g} = {O, X, Y, g} := by
-- proof
  apply StatMech.Walls.gc15_sd3 G O X Y g hOX hOY hOg hXY hXg hYg

/--
[gc15_sd4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_sd4_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq W]
  {O X Y g : W}
-- given
  (hOX : O ≠ X)
  (hOY : O ≠ Y)
  (hOg : O ≠ g)
  (hXY : X ≠ Y)
  (hXg : X ≠ g)
  (hYg : Y ≠ g) :
-- imply
  ({O, g} : Finset W) ∆ {X, g} ∆ {Y, g} = {O, X, Y, g} := by
-- proof
  apply StatMech.Walls.gc15_sd4 G O X Y g hOX hOY hOg hXY hXg hYg

/--
[gc15_inner_fiber_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_inner_fiber_triple_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : ↥S.edgeFinset → ℕ}
  {A B C : Finset V} :
-- imply
  (∑ K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}, ((if sources S (ofEdgeFun S K.1.1) = A then weight S β J (ofEdgeFun S K.1.1) else 0) * (if sources S (ofEdgeFun S K.1.2) = B then weight S β J (ofEdgeFun S K.1.2) else 0)) * (if sources S (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) = C then weight S β J (ofEdgeFun S fun e => m e - K.1.1 e - K.1.2 e) else 0)) = gc15_tFiber S β J A B C m := by
-- proof
  apply StatMech.Walls.gc15_inner_fiber_triple G S β J m A B C

/--
[gc15_summable_tFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_summable_tFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V} :
-- imply
  Summable (gc15_tFiber S β J A B C) := by
-- proof
  apply StatMech.Walls.gc15_summable_tFiber G S β J A B C

/--
[gc15_sourceTripleSum_eq_tFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_sourceTripleSum_eq_tFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B C : Finset V} :
-- imply
  sourceTripleSum S β J A B C = ∑' m, gc15_tFiber S β J A B C m := by
-- proof
  apply StatMech.Walls.gc15_sourceTripleSum_eq_tFiber G S β J A B C

/--
[gc15_Z0_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_Z0_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
-- given
  (β h : ℝ) :
-- imply
  0 < gc15_Z0 G β h := by
-- proof
  apply StatMech.Walls.gc15_Z0_pos G S β h

/--
[gc15_u3_ghost_expectationJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_u3_ghost_expectationJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y = expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o} : Finset V).map someEmb)) * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({x, y} : Finset V).map someEmb) - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb) * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb)) - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, y} : Finset V).map someEmb) * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({x} : Finset V).map someEmb)) + 2 * (expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o} : Finset V).map someEmb)) * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({x} : Finset V).map someEmb)) * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb))) := by
-- proof
  apply StatMech.Walls.gc15_u3_ghost_expectationJ G S β h o x y hox hoy hxy

/--
[gc15_u3_currentSum_poly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_u3_currentSum_poly_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = (gc15_Z0 G β h) ^ 2 * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o} : Finset V).map someEmb)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({x, y} : Finset V).map someEmb) - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb)) - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, y} : Finset V).map someEmb) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({x} : Finset V).map someEmb)) + 2 * (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o} : Finset V).map someEmb)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({x} : Finset V).map someEmb)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb))) := by
-- proof
  apply StatMech.Walls.gc15_u3_currentSum_poly G S β h o x y hox hoy hxy

/--
[gc15_gsingle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_gsingle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {a : V} :
-- imply
  insert (none : Option V) (({a} : Finset V).map someEmb) = ({some a, none} : Finset (Option V)) := by
-- proof
  apply StatMech.Walls.gc15_gsingle G S a

/--
[gc15_gpair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_gpair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {a b : V} :
-- imply
  (({a, b} : Finset V).map someEmb) = ({some a, some b} : Finset (Option V)) := by
-- proof
  apply StatMech.Walls.gc15_gpair G S a b

/--
[gc15_gquad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_gquad_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V} :
-- imply
  insert (none : Option V) (({o, x, y} : Finset V).map someEmb) = ({some o, some x, some y, none} : Finset (Option V)) := by
-- proof
  apply StatMech.Walls.gc15_gquad G S o x y

/--
[gc15_marks_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_marks_distinct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (some o ≠ some x) ∧ (some o ≠ some y) ∧ (some o ≠ (none : Option V)) ∧ (some x ≠ some y) ∧ (some x ≠ (none : Option V)) ∧ (some y ≠ (none : Option V)) := by
-- proof
  apply StatMech.Walls.gc15_marks_distinct G S hox hoy hxy

/--
[gc15_u3_eq_tsum_threeGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_u3_eq_tsum_threeGap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = ∑' m, gc15_threeGap G β h o x y m := by
-- proof
  apply StatMech.Walls.gc15_u3_eq_tsum_threeGap G S β h o x y hox hoy hxy

/--
[gc15_ursell_nonpos_of_perConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_ursell_nonpos_of_perConfig_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hsign : gc15_PerConfigUrsellSign G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc15_ursell_nonpos_of_perConfig G S β h o x y hox hoy hxy hsign

/--
[gc15_ghs_of_perConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_ghs_of_perConfig_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y) :
-- imply
  GHSThreePointSym G β h o := by
-- proof
  apply StatMech.Walls.gc15_ghs_of_perConfig G S β h hβ hh o hsign

/--
[gc15_aizenman_barsky_of_perConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_aizenman_barsky_of_perConfig_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Walls.gc15_aizenman_barsky_of_perConfig G S β h hβ hh o J hsign hfactor

/--
[gc15_distinct_ursell_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_distinct_ursell_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc15_distinct_ursell_nonpos G S β h o hsign hox hoy hxy

/--
[gc15_threeGap_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean)
-/
@[path]
private lemma gc15_threeGap_vanish_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : SimpleGraph V}
  [DecidableRel S.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m) ≠ ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  gc15_threeGap G β h o x y m = 0 := by
-- proof
  apply StatMech.Walls.gc15_threeGap_vanish G S β h o x y hox hoy hxy m hm


-- created on 2026-10-23
