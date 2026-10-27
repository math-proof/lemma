import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kwd_crosscountparity.Part3
open Finset Set SimpleGraph StatMech.Lattice StatMech StatMech.Walls


/--
[kwd_crossCount_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCount_nil_eq
  {G : SimpleGraph V}
  {B : Sym2 V → Bool}
  {x : V} :
-- imply
  kwd_crossCount B (SimpleGraph.Walk.nil : G.Walk x x) = 0 := by
-- proof
  apply StatMech.Walls.kwd_crossCount_nil B x

/--
[kwd_crossCount_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCount_cons_eq
  {G : SimpleGraph V}
  {B : Sym2 V → Bool}
  {a b c : V}
  {p : G.Walk b c}
-- given
  (hab : G.Adj a b) :
-- imply
  kwd_crossCount B (SimpleGraph.Walk.cons hab p) = (if B s(a, b) then 1 else 0) + kwd_crossCount B p := by
-- proof
  apply StatMech.Walls.kwd_crossCount_cons B hab p

/--
[kwd_crossCount_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCount_append_eq
  {G : SimpleGraph V}
  {B : Sym2 V → Bool}
  {x y z : V}
  {p : G.Walk x y}
  {q : G.Walk y z} :
-- imply
  kwd_crossCount B (p.append q) = kwd_crossCount B p + kwd_crossCount B q := by
-- proof
  apply StatMech.Walls.kwd_crossCount_append B p q

/--
[kwd_crossCount_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCount_reverse_eq
  {G : SimpleGraph V}
  {B : Sym2 V → Bool}
  {x y : V}
  {w : G.Walk x y} :
-- imply
  kwd_crossCount B w.reverse = kwd_crossCount B w := by
-- proof
  apply StatMech.Walls.kwd_crossCount_reverse B w

/--
[kwd_sideBoundary_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_sideBoundary_mk_eq
  {S : V → Bool}
  {x y : V} :
-- imply
  kwd_sideBoundary S s(x, y) = (S x != S y) := by
-- proof
  apply StatMech.Walls.kwd_sideBoundary_mk S x y

/--
[kwd_crossCount_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCount_parity_eq
  {G : SimpleGraph V}
  {S : V → Bool}
  {x y : V}
  {w : G.Walk x y} :
-- imply
  Even (kwd_crossCount (kwd_sideBoundary S) w) ↔ (S x = S y) := by
-- proof
  apply StatMech.Walls.kwd_crossCount_parity S w

/--
[kwd_crossCount_parity_eq_of_sameEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCount_parity_eq_of_sameEndpoints_eq
  {G : SimpleGraph V}
  {S : V → Bool}
  {x y : V}
  {w₁ w₂ : G.Walk x y} :
-- imply
  kwd_crossCount (kwd_sideBoundary S) w₁ % 2 = kwd_crossCount (kwd_sideBoundary S) w₂ % 2 := by
-- proof
  apply StatMech.Walls.kwd_crossCount_parity_eq_of_sameEndpoints S w₁ w₂

/--
[kwd_crossCount_even_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCount_even_of_closed_eq
  {G : SimpleGraph V}
  {S : V → Bool}
  {x : V}
  {w : G.Walk x x} :
-- imply
  Even (kwd_crossCount (kwd_sideBoundary S) w) := by
-- proof
  apply StatMech.Walls.kwd_crossCount_even_of_closed S w

/--
[kwd_sideBool_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_sideBool_eq_true_eq
  {S : Set (Site 2)}
  {v : Site 2} :
-- imply
  kwd_sideBool S v = true ↔ v ∈ S := by
-- proof
  apply StatMech.Walls.kwd_sideBool_eq_true S v

/--
[kwd_crossCountZ2_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCountZ2_eq_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  kwd_crossCountZ2 S w = kwd_crossCount (kwd_sideBoundary (kwd_sideBool S)) w := by
-- proof
  apply StatMech.Walls.kwd_crossCountZ2_eq S w

/--
[kwd_crossCountZ2_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCountZ2_parity_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  Even (kwd_crossCountZ2 S w) ↔ (x ∈ S ↔ y ∈ S) := by
-- proof
  apply StatMech.Walls.kwd_crossCountZ2_parity S w

/--
[kwd_crossCountZ2_even_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCountZ2_even_of_closed_eq
  {S : Set (Site 2)}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x} :
-- imply
  Even (kwd_crossCountZ2 S w) := by
-- proof
  apply StatMech.Walls.kwd_crossCountZ2_even_of_closed S w

/--
[kwd_crossCountZ2_odd_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean)
-/
@[path]
private lemma kwd_crossCountZ2_odd_of_separated_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ Even (kwd_crossCountZ2 S w) := by
-- proof
  apply StatMech.Walls.kwd_crossCountZ2_odd_of_separated S hx hy w


-- created on 2026-10-23
