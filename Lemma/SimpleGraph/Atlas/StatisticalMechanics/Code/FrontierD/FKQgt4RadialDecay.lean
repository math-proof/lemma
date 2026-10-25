import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part4
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFreeTwoPoint_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_pos_eq
  {q : Real}
  {x : Site 2}
-- given
  (hq : 4 < q) :
-- imply
  0 < fkQgt4CriticalFreeTwoPoint hq x := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_pos hq x

/--
[fkQgt4CriticalFreeTwoPoint_add_supermultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_add_supermultiplicative_eq
  {q : Real}
  {x y : Site 2}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq x * fkQgt4CriticalFreeTwoPoint hq y <= fkQgt4CriticalFreeTwoPoint hq (x + y) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_add_supermultiplicative hq x y

/--
[fkQgt4CriticalFreeTwoPoint_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_boxSym_eq
  {q : Real}
  {S : FK.BoxSym 2}
  {x : Site 2}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq (S.τ x) = fkQgt4CriticalFreeTwoPoint hq x := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_boxSym hq S x

/--
[fkQgt4NonnegativeSite_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4NonnegativeSite_apply_eq
  {x : Site 2}
  {i : Fin 2} :
-- imply
  fkQgt4NonnegativeSite x i = ((x i).natAbs : Int) := by
-- proof
  apply StatMech.FrontierD.fkQgt4NonnegativeSite_apply x i

/--
[fkQgt4CoordinateSignBoxSym_normalizes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4CoordinateSignBoxSym_normalizes_eq
  {x : Site 2} :
-- imply
  (fkQgt4CoordinateSignBoxSym (fun i => decide (x i < 0))).τ x = fkQgt4NonnegativeSite x := by
-- proof
  apply StatMech.FrontierD.fkQgt4CoordinateSignBoxSym_normalizes x

/--
[fkQgt4SiteSphere_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4SiteSphere_card_le_eq
  {n : Nat} :
-- imply
  (fkQgt4SiteSphere n).card <= (2 * n + 1) ^ 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SiteSphere_card_le n

/--
[fkQgt4Nonnegative_add_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4Nonnegative_add_swap_eq
  {x : Site 2} :
-- imply
  fkQgt4NonnegativeSite x + (FK.rot_permBoxSym 2 (Equiv.swap (0 : Fin 2) 1)).τ (fkQgt4NonnegativeSite x) = fkQgt4ExactDiagonalSite (fkQgt4SiteRadius x) := by
-- proof
  apply StatMech.FrontierD.fkQgt4Nonnegative_add_swap x

/--
[fkQgt4CriticalFreeTwoPoint_sq_le_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_sq_le_diagonal_eq
  {q : Real}
  {x : Site 2}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeTwoPoint hq x ^ 2 <= fkQgt4CriticalFreeExactDiagonalTwoPoint hq (fkQgt4SiteRadius x) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_sq_le_diagonal hq x

/--
[fkQgt4CriticalFreeTwoPoint_eventually_exponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTwoPoint_eventually_exponential_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  exists N : Nat, forall x : Site 2, N <= fkQgt4SiteRadius x -> fkQgt4CriticalFreeTwoPoint hq x <= Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) * (fkQgt4SiteRadius x : Real)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTwoPoint_eventually_exponential hq hpos

/--
[fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4RadialDecay.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  exists N : Nat, forall n : Nat, N <= n -> ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkQgt4CriticalFreeSphereConnectionEvent n) <= ((2 * n + 1 : Nat) : Real) ^ 2 * Real.exp (-(fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4) * (n : Real)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential hq hpos


-- created on 2026-10-23
