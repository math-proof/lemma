import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusResiduePotential
open StatMech StatMech.FrontierD StatMech.FrontierD.IntegralSquareTorusCycle


/--
[residueHorizontalCoeff_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueHorizontalCoeff_cast_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {z : ZMod L × ZMod L}
-- given
  (hx : (p : Int) ∣ C.xFlux (-1)) :
-- imply
  (C.residueHorizontalCoeff p z : ZMod p) = (C.horizontal z : ZMod p) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueHorizontalCoeff_cast C p hx z

/--
[residueVerticalCoeff_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueVerticalCoeff_cast_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {z : ZMod L × ZMod L}
-- given
  (hy : (p : Int) ∣ C.yFlux (-1)) :
-- imply
  (C.residueVerticalCoeff p z : ZMod p) = (C.vertical z : ZMod p) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueVerticalCoeff_cast C p hy z

/--
[abs_residueHorizontalCoeff_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma abs_residueHorizontalCoeff_lt_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {z : ZMod L × ZMod L} :
-- imply
  |C.residueHorizontalCoeff p z| < (p : Int) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.abs_residueHorizontalCoeff_lt C p z

/--
[abs_residueVerticalCoeff_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma abs_residueVerticalCoeff_lt_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {z : ZMod L × ZMod L} :
-- imply
  |C.residueVerticalCoeff p z| < (p : Int) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.abs_residueVerticalCoeff_lt C p z

/--
[residueHorizontalCoeff_eq_zero_of_horizontal_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueHorizontalCoeff_eq_zero_of_horizontal_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {z : ZMod L × ZMod L}
-- given
  (hx : (p : Int) ∣ C.xFlux (-1))
  (hz : C.horizontal z = 0) :
-- imply
  C.residueHorizontalCoeff p z = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueHorizontalCoeff_eq_zero_of_horizontal_eq_zero C p hx z hz

/--
[residueVerticalCoeff_eq_zero_of_vertical_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueVerticalCoeff_eq_zero_of_vertical_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {z : ZMod L × ZMod L}
-- given
  (hy : (p : Int) ∣ C.yFlux (-1))
  (hz : C.vertical z = 0) :
-- imply
  C.residueVerticalCoeff p z = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueVerticalCoeff_eq_zero_of_vertical_eq_zero C p hy z hz

/--
[residueHorizontalCoeff_ne_zero_of_horizontal_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueHorizontalCoeff_ne_zero_of_horizontal_eq_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [Fact (1 < p)]
  {z : ZMod L × ZMod L}
-- given
  (hx : (p : Int) ∣ C.xFlux (-1))
  (hz : C.horizontal z = 1) :
-- imply
  C.residueHorizontalCoeff p z ≠ 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueHorizontalCoeff_ne_zero_of_horizontal_eq_one C p hx z hz

/--
[residueHorizontalCoeff_ne_zero_of_horizontal_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueHorizontalCoeff_ne_zero_of_horizontal_eq_neg_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [Fact (1 < p)]
  {z : ZMod L × ZMod L}
-- given
  (hx : (p : Int) ∣ C.xFlux (-1))
  (hz : C.horizontal z = -1) :
-- imply
  C.residueHorizontalCoeff p z ≠ 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueHorizontalCoeff_ne_zero_of_horizontal_eq_neg_one C p hx z hz

/--
[residueVerticalCoeff_ne_zero_of_vertical_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueVerticalCoeff_ne_zero_of_vertical_eq_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [Fact (1 < p)]
  {z : ZMod L × ZMod L}
-- given
  (hy : (p : Int) ∣ C.yFlux (-1))
  (hz : C.vertical z = 1) :
-- imply
  C.residueVerticalCoeff p z ≠ 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueVerticalCoeff_ne_zero_of_vertical_eq_one C p hy z hz

/--
[residueVerticalCoeff_ne_zero_of_vertical_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueVerticalCoeff_ne_zero_of_vertical_eq_neg_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [Fact (1 < p)]
  {z : ZMod L × ZMod L}
-- given
  (hy : (p : Int) ∣ C.yFlux (-1))
  (hz : C.vertical z = -1) :
-- imply
  C.residueVerticalCoeff p z ≠ 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueVerticalCoeff_ne_zero_of_vertical_eq_neg_one C p hy z hz

/--
[residueCoeff_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma residueCoeff_divergence_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p]
  {z : ZMod L × ZMod L} :
-- imply
  C.residueHorizontalCoeff p z + C.residueVerticalCoeff p z - C.residueHorizontalCoeff p (z.1 - 1, z.2) - C.residueVerticalCoeff p (z.1, z.2 - 1) = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.residueCoeff_divergence C p z

/--
[sum_residueHorizontalCoeff_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma sum_residueHorizontalCoeff_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p] :
-- imply
  ∑ z : ZMod L × ZMod L, C.residueHorizontalCoeff p z = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.sum_residueHorizontalCoeff_eq_zero C p

/--
[sum_residueVerticalCoeff_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusResiduePotential.lean)
-/
@[path]
private lemma sum_residueVerticalCoeff_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : Nat}
  [NeZero p] :
-- imply
  ∑ z : ZMod L × ZMod L, C.residueVerticalCoeff p z = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.sum_residueVerticalCoeff_eq_zero C p


-- created on 2026-10-23
