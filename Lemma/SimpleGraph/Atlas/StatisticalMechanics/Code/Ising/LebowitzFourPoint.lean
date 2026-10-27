import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzFourPoint
open Finset Filter Set StatMech StatMech.Ising


/--
[wJ_pointField_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma wJ_pointField_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {l : V}
  {t : Real}
  {s : ConfigSpace V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  wJ E J (lebowitzPointField l t) s = wJ E J (fun _ => 0) s * (Real.cosh t + spin s l * Real.sinh t) := by
-- proof
  apply StatMech.Ising.wJ_pointField_eq E J l t s

/--
[ZJ_pointField_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma ZJ_pointField_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {l : V}
  {t : Real}
-- given
  (J : Sym2 V -> Real) :
-- imply
  ZJ E J (lebowitzPointField l t) = Real.cosh t * ZJ E J (fun _ => 0) := by
-- proof
  apply StatMech.Ising.ZJ_pointField_eq E J l t

/--
[expJ_pointField_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma expJ_pointField_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {l : V}
  {t : Real}
-- given
  (J : Sym2 V -> Real)
  (f : ConfigSpace V -> Real) :
-- imply
  expJ E J (lebowitzPointField l t) f = expJ E J (fun _ => 0) f + Real.tanh t * expJ E J (fun _ => 0) (fun s => f s * spin s l) := by
-- proof
  apply StatMech.Ising.expJ_pointField_eq E J l t f

/--
[expJ_zero_three_spin_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma expJ_zero_three_spin_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  expJ E J (fun _ => 0) (fun s => spin s x * (spin s y * spin s z)) = 0 := by
-- proof
  apply StatMech.Ising.expJ_zero_three_spin_eq_zero E J x y z hxy hxz hyz

/--
[expJ_pointField_two_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma expJ_pointField_two_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y l : V}
  {t : Real}
-- given
  (J : Sym2 V -> Real)
  (hxl : x ≠ l)
  (hyl : y ≠ l)
  (hxy : x ≠ y) :
-- imply
  expJ E J (lebowitzPointField l t) (fun s => spin s x * spin s y) = expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.Ising.expJ_pointField_two_eq E J x y l hxl hyl hxy t

/--
[expJ_pointField_one_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma expJ_pointField_one_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x l : V}
  {t : Real}
-- given
  (J : Sym2 V -> Real) :
-- imply
  expJ E J (lebowitzPointField l t) (fun s => spin s x) = Real.tanh t * expJ E J (fun _ => 0) (fun s => spin s x * spin s l) := by
-- proof
  apply StatMech.Ising.expJ_pointField_one_eq E J x l t

/--
[expJ_pointField_three_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma expJ_pointField_three_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {i j k l : V}
  {t : Real}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  expJ E J (lebowitzPointField l t) (fun s => spin s i * (spin s j * spin s k)) = Real.tanh t * expJ E J (fun _ => 0) (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
-- proof
  apply StatMech.Ising.expJ_pointField_three_eq E J i j k l hij hik hjk t

/--
[lebowitz_four_point_with_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma lebowitz_four_point_with_parameter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
  {q : Real}
-- given
  (K : Sym2 V -> Real)
  (hK : ∀ e, 0 ≤ K e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l)
  (hq0 : 0 < q)
  (hq1 : q < 1) :
-- imply
  grahamUrsell4 G.edgeFinset K i j k l + 2 * q ^ 2 * (grahamTwoPoint G.edgeFinset K i l * grahamTwoPoint G.edgeFinset K j l * grahamTwoPoint G.edgeFinset K k l) ≤ 0 := by
-- proof
  apply StatMech.Ising.lebowitz_four_point_with_parameter G K hK i j k l hij hik hil hjk hjl hkl q hq0 hq1

/--
[lebowitz_four_point_le_leading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma lebowitz_four_point_le_leading_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (K : Sym2 V -> Real)
  (hK : ∀ e, 0 ≤ K e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  grahamUrsell4 G.edgeFinset K i j k l ≤ -2 * (grahamTwoPoint G.edgeFinset K i l * grahamTwoPoint G.edgeFinset K j l * grahamTwoPoint G.edgeFinset K k l) := by
-- proof
  apply StatMech.Ising.lebowitz_four_point_le_leading G K hK i j k l hij hik hil hjk hjl hkl

/--
[lebowitz_four_point_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean)
-/
@[path]
private lemma lebowitz_four_point_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (K : Sym2 V -> Real)
  (hK : ∀ e, 0 ≤ K e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  grahamUrsell4 G.edgeFinset K i j k l ≤ 0 := by
-- proof
  apply StatMech.Ising.lebowitz_four_point_nonpos G K hK i j k l hij hik hil hjk hjl hkl


-- created on 2026-10-23
