import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc8crossparityleftregion.Part2
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc8_one_le_of_not_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_one_le_of_not_even_eq
  {n : ℕ}
-- given
  (h : ¬ Even n) :
-- imply
  1 ≤ n := by
-- proof
  apply StatMech.Walls.jc8_one_le_of_not_even h

/--
[jc8_crossCount_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossCount_parity_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S) := by
-- proof
  apply StatMech.Walls.jc8_crossCount_parity S w

/--
[jc8_crossCount_parity_eq_of_sameEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossCount_parity_eq_of_sameEndpoints_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w₁ w₂ : (hypercubicLattice 2).Walk x y} :
-- imply
  crossCount S w₁ % 2 = crossCount S w₂ % 2 := by
-- proof
  apply StatMech.Walls.jc8_crossCount_parity_eq_of_sameEndpoints S w₁ w₂

/--
[jc8_crossCount_even_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossCount_even_of_closed_eq
  {S : Set (Site 2)}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x} :
-- imply
  Even (crossCount S w) := by
-- proof
  apply StatMech.Walls.jc8_crossCount_even_of_closed S w

/--
[jc8_crossCount_odd_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossCount_odd_of_separated_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ Even (crossCount S w) := by
-- proof
  apply StatMech.Walls.jc8_crossCount_odd_of_separated S hx hy w

/--
[jc8_crossCount_ge_one_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossCount_ge_one_of_separated_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  1 ≤ crossCount S w := by
-- proof
  apply StatMech.Walls.jc8_crossCount_ge_one_of_separated S hx hy w

/--
[jc8_orbitLoop_crossCount_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_orbitLoop_crossCount_even_eq
  {K : Set (Site 2)}
  {e : Dart}
  {S : Set (Site 2)}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  Even (crossCount S (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Walls.jc8_orbitLoop_crossCount_even K hK e he S

/--
[jc8_crossCount_odd_of_opposite_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossCount_odd_of_opposite_leftRegion_eq
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hx : x ∈ jec_leftRegion (olb_orbitLoop K hK e he))
  (hy : y ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
-- imply
  ¬ Even (crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w) := by
-- proof
  apply StatMech.Walls.jc8_crossCount_odd_of_opposite_leftRegion K hK e he w hx hy

/--
[jc8_crossCount_ge_one_of_opposite_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossCount_ge_one_of_opposite_leftRegion_eq
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hx : x ∈ jec_leftRegion (olb_orbitLoop K hK e he))
  (hy : y ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
-- imply
  1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w := by
-- proof
  apply StatMech.Walls.jc8_crossCount_ge_one_of_opposite_leftRegion K hK e he w hx hy

/--
[jc8_leftRegion_sameSide_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_leftRegion_sameSide_of_even_eq
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (heven : Even (crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w)) :
-- imply
  (x ∈ jec_leftRegion (olb_orbitLoop K hK e he) ↔ y ∈ jec_leftRegion (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Walls.jc8_leftRegion_sameSide_of_even K hK e he w heven

/--
[jc8_crossParityLeftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossParityLeftRegion_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  jc8_CrossParityLeftRegion K hK e he := by
-- proof
  apply StatMech.Walls.jc8_crossParityLeftRegion K hK e he

/--
[jc8_crossCount_parity_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_crossCount_parity_self_eq
  {S : Set (Site 2)}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x} :
-- imply
  Even (crossCount S w) := by
-- proof
  apply StatMech.Walls.jc8_crossCount_parity_self S w

/--
[jc8_leftRegion_loop_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8crossparityleftregion.lean)
-/
@[path]
private lemma jc8_leftRegion_loop_even_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  Even (crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Walls.jc8_leftRegion_loop_even K hK e he


-- created on 2026-10-23
