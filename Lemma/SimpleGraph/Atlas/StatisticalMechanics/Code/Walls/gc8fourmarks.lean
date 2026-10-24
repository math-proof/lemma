import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc8fourmarks
open Finset BigOperators SimpleGraph StatMech StatMech.Walls


/--
[gc8_fourMarks_pairwise_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_pairwise_distinct_eq
  [Fintype V]
  [DecidableEq V]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (some o ≠ some x) ∧ (some o ≠ some y) ∧ (some o ≠ (none : Option V)) ∧ (some x ≠ some y) ∧ (some x ≠ (none : Option V)) ∧ (some y ≠ (none : Option V)) := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_pairwise_distinct o x y hox hoy hxy

/--
[gc8_fourMarks_eq_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_eq_explicit_eq
  [Fintype V]
  [DecidableEq V]
  {o x y : V} :
-- imply
  insert (none : Option V) (({o, x, y} : Finset V).map someEmb) = ({none, some o, some x, some y} : Finset (Option V)) := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_eq_explicit o x y

/--
[gc8_fourMarks_card_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_card_explicit_eq
  [Fintype V]
  [DecidableEq V]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (({none, some o, some x, some y} : Finset (Option V))).card = 4 := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_card_explicit o x y hox hoy hxy

/--
[gc8_fourMarks_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_card_eq
  [Fintype V]
  [DecidableEq V]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card = 4 := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_card o x y hox hoy hxy

/--
[gc8_fourMarks_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_even_eq
  [Fintype V]
  [DecidableEq V]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_even o x y hox hoy hxy

/--
[gc8_fourMarks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_eq
  [Fintype V]
  [DecidableEq V]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  ((some o ≠ some x) ∧ (some o ≠ some y) ∧ (some o ≠ (none : Option V)) ∧ (some x ≠ some y) ∧ (some x ≠ (none : Option V)) ∧ (some y ≠ (none : Option V))) ∧ (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card = 4 ∧ Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card := by
-- proof
  apply StatMech.Walls.gc8_fourMarks o x y hox hoy hxy

/--
[gc8_fourMarks_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_dichotomy_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 (Option V)}
  {K : Finset ι}
  {o x y : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbdry : sources ends K = ({some o, some x, some y, none} : Finset (Option V)))
  (hog_disc : ¬ connK ends K (some o) none) :
-- imply
  ((connK ends K (some o) (some x) ∧ connK ends K (some y) none) ∨ (connK ends K (some o) (some y) ∧ connK ends K (some x) none)) ∧ ¬ ((connK ends K (some o) (some x) ∧ connK ends K (some y) none) ∧ (connK ends K (some o) (some y) ∧ connK ends K (some x) none)) := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_dichotomy ends K hnd o x y hox hoy hxy hbdry hog_disc

/--
[gc8_fourMarks_trichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_trichotomy_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 (Option V)}
  {K : Finset ι}
  {o x y : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbdry : sources ends K = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  (connK ends K (some o) none) ∨ (connK ends K (some o) (some x) ∧ connK ends K (some y) none) ∨ (connK ends K (some o) (some y) ∧ connK ends K (some x) none) := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_trichotomy ends K hnd o x y hox hoy hxy hbdry

/--
[gc8_fourMarks_cluster_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_cluster_even_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 (Option V)}
  {K : Finset ι}
  {o x y u : V}
-- given
  (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hbdry : sources ends K = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  Even (#(({some o, some x, some y, none} : Finset (Option V)) ∩ (compOf ends K (some u)))) := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_cluster_even ends K hnd o x y u hbdry

/--
[gc8_fourMarks_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι] :
-- imply
  ((some (0 : Fin 3) ≠ some 1) ∧ (some (0 : Fin 3) ≠ some 2) ∧ (some (0 : Fin 3) ≠ (none : Option (Fin 3))) ∧ (some (1 : Fin 3) ≠ some 2) ∧ (some (1 : Fin 3) ≠ (none : Option (Fin 3))) ∧ (some (2 : Fin 3) ≠ (none : Option (Fin 3)))) ∧ (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)).card = 4 ∧ Even (insert (none : Option (Fin 3)) (({0, 1, 2} : Finset (Fin 3)).map someEmb)).card := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_nonvacuous

/--
[gc8_fourMarks_griffiths_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_griffiths_step_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {eS cS eΛ : ℝ}
-- given
  (hSnn : 0 ≤ eS)
  (hcSnn : 0 ≤ cS)
  (hgriff : eS ≤ eΛ) :
-- imply
  eΛ * (eS * cS) ≥ eS ^ 2 * cS := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_griffiths_step eS cS eΛ hSnn hcSnn hgriff

/--
[gc8_fourMarks_ursell_nonpos_of_eqSwi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8fourmarks.lean)
-/
@[path]
private lemma gc8_fourMarks_ursell_nonpos_of_eqSwi_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hid : gc6_EqSwiIdentity G β h o) :
-- imply
  GhcEqGap.eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gc8_fourMarks_ursell_nonpos_of_eqSwi G β h hβ hh o hid x y


-- created on 2026-10-23
