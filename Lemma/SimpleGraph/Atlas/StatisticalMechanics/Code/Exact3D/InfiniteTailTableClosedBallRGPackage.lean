import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.InfiniteTailTableClosedBallRGPackage
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage


/--
[certificate_eq_closedBallRG_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_eq_closedBallRG_certificate_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.certificate scale = P.closedBallRG.certificate scale M := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_eq_closedBallRG_certificate P scale

/--
[tableCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tableCertifiedTotalBound = P.tableWitness.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tableCertifiedTotalBound_eq P

/--
[tableFiniteBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tableFiniteBudget_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tableFiniteBudget = P.tableWitness.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tableFiniteBudget_eq P

/--
[tablePrefixBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tablePrefixBudget_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tablePrefixBudget = P.tableWitness.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tablePrefixBudget_eq P

/--
[tailTotalTsum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tailTotalTsum = P.tableWitness.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_eq P

/--
[tailBudget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailBudget_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tailBudget = P.tableWitness.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailBudget_eq P

/--
[tailContribution_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailContribution_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tailContribution = P.tableWitness.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailContribution_eq P

/--
[closedBallResidual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallResidual_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.closedBallResidual = P.closedBallRG.closedBall.residual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallResidual_eq P

/--
[closedBallRadius_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallRadius_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.closedBallRadius = P.closedBallRG.closedBall.radius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallRadius_eq P

/--
[closedBallCenter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallCenter_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.closedBallCenter = P.closedBallRG.closedBall.center := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallCenter_eq P

/--
[closedBallContraction_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallContraction_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.closedBallContraction = P.closedBallRG.closedBall.contraction := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallContraction_eq P

/--
[closedBallFixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallFixedPoint_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.closedBallFixedPoint = P.closedBallRG.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallFixedPoint_eq P

/--
[closedBallRadius_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallRadius_nonneg_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  0 ≤ P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallRadius_nonneg P

/--
[closedBallResidual_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallResidual_bound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.closedBallContraction.map P.closedBallCenter).dist P.closedBallCenter ≤ P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallResidual_bound P

/--
[closedBallRadius_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallRadius_bound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.closedBallResidual + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallRadius_bound P

/--
[mapsClosedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma mapsClosedBall_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  FinitePlusTailState.MapsClosedBall P.closedBallContraction.map P.closedBallCenter P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.mapsClosedBall P

/--
[closedBallFixedPoint_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallFixedPoint_mem_closedBall_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  FinitePlusTailState.ClosedBall P.closedBallCenter P.closedBallRadius P.closedBallFixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallFixedPoint_mem_closedBall P

/--
[fixedPoint_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma fixedPoint_mem_closedBall_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  FinitePlusTailState.ClosedBall P.closedBallCenter P.closedBallRadius P.closedBallRG.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.fixedPoint_mem_closedBall P

/--
[closedBallFixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallFixedPoint_isFixed_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.closedBallContraction.map P.closedBallFixedPoint = P.closedBallFixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallFixedPoint_isFixed P

/--
[closedBall_fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBall_fixedPoint_isFixed_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.closedBallContraction.map P.closedBallRG.closedBall.fixedPoint = P.closedBallRG.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBall_fixedPoint_isFixed P

/--
[tableCertifiedTotalBound_le_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_le_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tableCertifiedTotalBound ≤ P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tableCertifiedTotalBound_le_closedBallResidual P

/--
[tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tableCertifiedTotalBound = P.tablePrefixBudget + P.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tableCertifiedTotalBound_eq_tablePrefixBudget_add_tailBudget P

/--
[tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {prefixBound tailBound' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hprefix : P.tablePrefixBudget ≤ prefixBound)
  (htail : P.tailBudget ≤ tailBound') :
-- imply
  P.tableCertifiedTotalBound ≤ prefixBound + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBudget P hprefix htail

/--
[tailTotalTsum_le_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_tableCertifiedTotalBound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tailTotalTsum ≤ P.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_le_tableCertifiedTotalBound P

/--
[tailTotalTsum_le_tablePrefixBudget_add_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_tablePrefixBudget_add_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tailTotalTsum ≤ P.tablePrefixBudget + P.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_le_tablePrefixBudget_add_tailBudget P

/--
[tailTotalTsum_le_of_tableCertifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_of_tableCertifiedTotalBound_le_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {B : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hB : P.tableCertifiedTotalBound ≤ B) :
-- imply
  P.tailTotalTsum ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_le_of_tableCertifiedTotalBound_le P hB

/--
[tailTotalTsum_le_of_tablePrefixBudget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_of_tablePrefixBudget_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {prefixBound tailBound' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hprefix : P.tablePrefixBudget ≤ prefixBound)
  (htail : P.tailBudget ≤ tailBound') :
-- imply
  P.tailTotalTsum ≤ prefixBound + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_le_of_tablePrefixBudget_tailBudget P hprefix htail

/--
[summable_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma summable_tailContribution_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  Summable P.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.summable_tailContribution P

/--
[tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tsum_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tailTotalTsum = ∑' a, P.tailContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_eq_tsum P

/--
[tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tail_tsum_nonneg_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  0 ≤ ∑' a, P.tailContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tail_tsum_nonneg P

/--
[tail_tsum_le_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tail_tsum_le_tableCertifiedTotalBound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (∑' a, P.tailContribution a) ≤ P.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tail_tsum_le_tableCertifiedTotalBound P

/--
[tail_tsum_le_of_tableCertifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tail_tsum_le_of_tableCertifiedTotalBound_le_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {B : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hB : P.tableCertifiedTotalBound ≤ B) :
-- imply
  (∑' a, P.tailContribution a) ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tail_tsum_le_of_tableCertifiedTotalBound_le P hB

/--
[tail_tsum_le_of_tablePrefixBudget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tail_tsum_le_of_tablePrefixBudget_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {prefixBound tailBound' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hprefix : P.tablePrefixBudget ≤ prefixBound)
  (htail : P.tailBudget ≤ tailBound') :
-- imply
  (∑' a, P.tailContribution a) ≤ prefixBound + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tail_tsum_le_of_tablePrefixBudget_tailBudget P hprefix htail

/--
[tail_tsum_le_tablePrefixBudget_add_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tail_tsum_le_tablePrefixBudget_add_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (∑' a, P.tailContribution a) ≤ P.tablePrefixBudget + P.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tail_tsum_le_tablePrefixBudget_add_tailBudget P

/--
[tailContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailContribution_nonneg_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {a : Coord}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  0 ≤ P.tailContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailContribution_nonneg P a

/--
[tailTotalTsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_nonneg_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  0 ≤ P.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_nonneg P

/--
[tableCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_nonneg_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  0 ≤ P.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tableCertifiedTotalBound_nonneg P

/--
[tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailBudget_nonneg_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  0 ≤ P.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailBudget_nonneg P

/--
[closedBallResidual_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma closedBallResidual_nonneg_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  0 ≤ P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.closedBallResidual_nonneg P

/--
[tailTotalTsum_le_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tailTotalTsum ≤ P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_le_closedBallResidual P

/--
[tail_tsum_le_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tail_tsum_le_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (∑' a, P.tailContribution a) ≤ P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tail_tsum_le_closedBallResidual P

/--
[tailTotalTsum_le_of_closedBallResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_of_closedBallResidual_le_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {B : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hB : P.closedBallResidual ≤ B) :
-- imply
  P.tailTotalTsum ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_le_of_closedBallResidual_le P hB

/--
[tail_tsum_le_of_closedBallResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tail_tsum_le_of_closedBallResidual_le_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {B : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hB : P.closedBallResidual ≤ B) :
-- imply
  (∑' a, P.tailContribution a) ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tail_tsum_le_of_closedBallResidual_le P hB

/--
[certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_thermalEigenvalue_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).thermalEigenvalue = P.closedBallRG.thermal := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_thermalEigenvalue_eq P scale

/--
[certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_scale_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).scale = scale := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_scale_eq P scale

/--
[certificate_fixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_fixedPoint_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).fixedPointData.fixedPoint = P.closedBallRG.closedBall.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_fixedPoint_eq P scale

/--
[certificate_R_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_R_map_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).R.map = P.closedBallContraction.map := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_R_map_eq P scale

/--
[certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_predictedExponent_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).predictedExponent = predictedNu scale P.closedBallRG.thermal := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_predictedExponent_eq P scale

/--
[certificate_fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_fixedPointEnclosure_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_fixedPointEnclosure P scale

/--
[certificate_finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_finiteCaseChecks_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_finiteCaseChecks P scale

/--
[certificate_tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_tailBounds_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_tailBounds P scale

/--
[certificate_linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_linearizationEnclosure_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_linearizationEnclosure P scale

/--
[certificate_hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_hyperbolicSplitting_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hyperbolicSplitting P scale

/--
[certificate_orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_orbitEntry_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.certificate scale).OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_orbitEntry P scale

/--
[certificate_fixedPoint_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_fixedPoint_mem_closedBall_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  FinitePlusTailState.ClosedBall P.closedBallCenter P.closedBallRadius (P.certificate scale).fixedPointData.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_fixedPoint_mem_closedBall P scale

/--
[certificate_iterate_mem_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_iterate_mem_closedBall_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {x : (P.certificate scale).H.carrier}
  {k : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hx : FinitePlusTailState.ClosedBall P.closedBallCenter P.closedBallRadius x) :
-- imply
  FinitePlusTailState.ClosedBall P.closedBallCenter P.closedBallRadius ((((P.certificate scale).R.map)^[k]) x) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_iterate_mem_closedBall P scale hx k

/--
[tableCertifiedTotalBound_plus_mul_radius_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_plus_mul_radius_le_radius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tableCertifiedTotalBound_plus_mul_radius_le_radius P

/--
[tailTotalTsum_plus_mul_radius_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tailTotalTsum_plus_mul_radius_le_radius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  P.tailTotalTsum + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tailTotalTsum_plus_mul_radius_le_radius P

/--
[tail_tsum_plus_mul_radius_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma tail_tsum_plus_mul_radius_le_radius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (∑' a, P.tailContribution a) + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.tail_tsum_plus_mul_radius_le_radius P

/--
[certificate_valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_bridge P scale correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_hasCriticalNu_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hν : HasCriticalNu M correlationLength (P.certificate scale).predictedExponent) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_hasCriticalNu P scale correlationLength hν

/--
[certificate_valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_valid_of_hasCriticalNu_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hν : HasCriticalNu M correlationLength (P.certificate scale).predictedExponent) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_hasCriticalNu P scale correlationLength hν

/--
[certificate_hasCriticalNu_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_hasCriticalNu_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hν : HasCriticalNu M correlationLength (P.certificate scale).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_hasCriticalNu P scale hν

/--
[certificate_hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_bridge P scale correlationLength hbridge

/--
[certificate_rgToExponentBridge_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_rgToExponentBridge_of_bridge_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_rgToExponentBridge_of_bridge_congr_predictedExponent P scale hpred hbridge

/--
[certificate_valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_valid_of_bridge_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  (P.certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_valid_of_bridge_congr_predictedExponent P scale hpred hbridge

/--
[certificate_hasCriticalNu_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma certificate_hasCriticalNu_of_bridge_congr_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hpred : (P.certificate scale).predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.certificate_hasCriticalNu_of_bridge_congr_predictedExponent P scale hpred hbridge

/--
[retarget_tableWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_tableWitness_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).tableWitness = P.tableWitness.retarget N := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_tableWitness P N

/--
[retarget_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_tailContribution_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).tailContribution = P.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_tailContribution P N

/--
[retarget_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_tailTotalTsum_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).tailTotalTsum = P.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_tailTotalTsum P N

/--
[retarget_closedBallRG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_closedBallRG_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).closedBallRG = P.closedBallRG := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_closedBallRG P N

/--
[retarget_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_tableCertifiedTotalBound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).tableCertifiedTotalBound = P.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_tableCertifiedTotalBound P N

/--
[retarget_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_tableFiniteBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).tableFiniteBudget = P.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_tableFiniteBudget P N

/--
[retarget_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_tablePrefixBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).tablePrefixBudget = P.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_tablePrefixBudget P N

/--
[retarget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).tailBudget = P.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_tailBudget P N

/--
[retarget_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).closedBallResidual = P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_closedBallResidual P N

/--
[retarget_closedBallRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_closedBallRadius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).closedBallRadius = P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_closedBallRadius P N

/--
[retarget_closedBallCenter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_closedBallCenter_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).closedBallCenter = P.closedBallCenter := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_closedBallCenter P N

/--
[retarget_closedBallContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_closedBallContraction_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).closedBallContraction = P.closedBallContraction := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_closedBallContraction P N

/--
[retarget_closedBallFixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_closedBallFixedPoint_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).closedBallFixedPoint = P.closedBallFixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_closedBallFixedPoint P N

/--
[retarget_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_certificate_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  (P.retarget N).certificate scale = (P.certificate scale).retarget N := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_certificate P N scale

/--
[retarget_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_predictedExponent_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n) :
-- imply
  ((P.retarget N).certificate scale).predictedExponent = (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_predictedExponent P N scale

/--
[retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  ((P.retarget N).certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_rgToExponentBridge P N scale hbridge hβc

/--
[retarget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_valid_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hvalid : (P.certificate scale).Valid correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  ((P.retarget N).certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_valid P N scale hvalid hβc

/--
[retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hν : HasCriticalNu M correlationLength (P.certificate scale).predictedExponent)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu N correlationLength ((P.retarget N).certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_hasCriticalNu P N scale hν hβc

/--
[retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_iff_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hβc : M.betaC = N.betaC) :
-- imply
  (P.certificate scale).RGToExponentBridge correlationLength ↔ ((P.retarget N).certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_rgToExponentBridge_iff P N scale hβc

/--
[retarget_valid_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_valid_iff_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hβc : M.betaC = N.betaC) :
-- imply
  (P.certificate scale).Valid correlationLength ↔ ((P.retarget N).certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_valid_iff P N scale hβc

/--
[retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_iff_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {N : CriticalModel κ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength (P.certificate scale).predictedExponent ↔ HasCriticalNu N correlationLength ((P.retarget N).certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.retarget_hasCriticalNu_iff P N scale hβc

/--
[with_tableWitness_tableWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tableWitness_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).tableWitness = W := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tableWitness P W hbudget

/--
[with_tableWitness_closedBallRG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_closedBallRG_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).closedBallRG = P.closedBallRG := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_closedBallRG P W hbudget

/--
[with_tableWitness_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tableCertifiedTotalBound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).tableCertifiedTotalBound = W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tableCertifiedTotalBound P W hbudget

/--
[with_tableWitness_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tableFiniteBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).tableFiniteBudget = W.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tableFiniteBudget P W hbudget

/--
[with_tableWitness_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tablePrefixBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).tablePrefixBudget = W.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tablePrefixBudget P W hbudget

/--
[with_tableWitness_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tailTotalTsum_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tailTotalTsum P W hbudget

/--
[with_tableWitness_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).tailBudget = W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tailBudget P W hbudget

/--
[with_tableWitness_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tailContribution_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tailContribution P W hbudget

/--
[with_tableWitness_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).closedBallResidual = P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_closedBallResidual P W hbudget

/--
[with_tableWitness_closedBallRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_closedBallRadius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).closedBallRadius = P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_closedBallRadius P W hbudget

/--
[with_tableWitness_closedBallCenter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_closedBallCenter_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).closedBallCenter = P.closedBallCenter := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_closedBallCenter P W hbudget

/--
[with_tableWitness_closedBallContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_closedBallContraction_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).closedBallContraction = P.closedBallContraction := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_closedBallContraction P W hbudget

/--
[with_tableWitness_closedBallFixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_closedBallFixedPoint_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).closedBallFixedPoint = P.closedBallFixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_closedBallFixedPoint P W hbudget

/--
[with_tableWitness_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_certificate_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (P.with_tableWitness W hbudget).certificate scale = P.certificate scale := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_certificate_eq P W hbudget scale

/--
[with_tableWitness_tailTotalTsum_le_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tailTotalTsum_le_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  W.tailTotalTsum ≤ P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tailTotalTsum_le_closedBallResidual P W hbudget

/--
[with_tableWitness_tail_tsum_le_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tail_tsum_le_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (∑' a, W.tailContribution a) ≤ P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tail_tsum_le_closedBallResidual P W hbudget

/--
[with_tableWitness_tableCertifiedTotalBound_plus_mul_radius_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tableCertifiedTotalBound_plus_mul_radius_le_radius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tableCertifiedTotalBound_plus_mul_radius_le_radius P W hbudget

/--
[with_tableWitness_tailTotalTsum_plus_mul_radius_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tailTotalTsum_plus_mul_radius_le_radius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  W.tailTotalTsum + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tailTotalTsum_plus_mul_radius_le_radius P W hbudget

/--
[with_tableWitness_tail_tsum_plus_mul_radius_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_tail_tsum_plus_mul_radius_le_radius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  (∑' a, W.tailContribution a) + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_tail_tsum_plus_mul_radius_le_radius P W hbudget

/--
[with_tableWitness_certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_certificate_predictedExponent_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual) :
-- imply
  ((P.with_tableWitness W hbudget).certificate scale).predictedExponent = (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_certificate_predictedExponent_eq P W hbudget scale

/--
[with_tableWitness_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_rgToExponentBridge_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
-- imply
  ((P.with_tableWitness W hbudget).certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_rgToExponentBridge P W hbudget scale hbridge

/--
[with_tableWitness_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_valid_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
  (hvalid : (P.certificate scale).Valid correlationLength) :
-- imply
  ((P.with_tableWitness W hbudget).certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_valid P W hbudget scale hvalid

/--
[with_tableWitness_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_hasCriticalNu_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hbudget : W.tableCertifiedTotalBound ≤ P.closedBallResidual)
  (hν : HasCriticalNu M correlationLength (P.certificate scale).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((P.with_tableWitness W hbudget).certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_hasCriticalNu P W hbudget scale hν

/--
[with_larger_closedBallRadius_tableWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_tableWitness_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).tableWitness = P.tableWitness := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_tableWitness P hradius

/--
[with_larger_closedBallRadius_closedBallRG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_closedBallRG_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).closedBallRG = P.closedBallRG.with_larger_radius hradius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_closedBallRG P hradius

/--
[with_larger_closedBallRadius_closedBallRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_closedBallRadius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).closedBallRadius = radius' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_closedBallRadius P hradius

/--
[with_larger_closedBallRadius_closedBallCenter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_closedBallCenter_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).closedBallCenter = P.closedBallCenter := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_closedBallCenter P hradius

/--
[with_larger_closedBallRadius_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).closedBallResidual = P.closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_closedBallResidual P hradius

/--
[with_larger_closedBallRadius_closedBallContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_closedBallContraction_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).closedBallContraction = P.closedBallContraction := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_closedBallContraction P hradius

/--
[with_larger_closedBallRadius_closedBallFixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_closedBallFixedPoint_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).closedBallFixedPoint = P.closedBallFixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_closedBallFixedPoint P hradius

/--
[with_larger_closedBallRadius_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_tableCertifiedTotalBound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).tableCertifiedTotalBound = P.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_tableCertifiedTotalBound P hradius

/--
[with_larger_closedBallRadius_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_tableFiniteBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).tableFiniteBudget = P.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_tableFiniteBudget P hradius

/--
[with_larger_closedBallRadius_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_tablePrefixBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).tablePrefixBudget = P.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_tablePrefixBudget P hradius

/--
[with_larger_closedBallRadius_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_tailTotalTsum_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).tailTotalTsum = P.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_tailTotalTsum P hradius

/--
[with_larger_closedBallRadius_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).tailBudget = P.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_tailBudget P hradius

/--
[with_larger_closedBallRadius_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_tailContribution_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).tailContribution = P.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_tailContribution P hradius

/--
[with_larger_closedBallRadius_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_certificate_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  (P.with_larger_closedBallRadius hradius).certificate scale = P.certificate scale := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_certificate_eq P hradius scale

/--
[with_larger_closedBallRadius_certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_certificate_predictedExponent_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius') :
-- imply
  ((P.with_larger_closedBallRadius hradius).certificate scale).predictedExponent = (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_certificate_predictedExponent_eq P hradius scale

/--
[with_larger_closedBallRadius_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_rgToExponentBridge_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius')
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
-- imply
  ((P.with_larger_closedBallRadius hradius).certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_rgToExponentBridge P hradius scale hbridge

/--
[with_larger_closedBallRadius_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_valid_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius')
  (hvalid : (P.certificate scale).Valid correlationLength) :
-- imply
  ((P.with_larger_closedBallRadius hradius).certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_valid P hradius scale hvalid

/--
[with_larger_closedBallRadius_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallRadius_hasCriticalNu_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {radius' : ℝ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hradius : P.closedBallRadius ≤ radius')
  (hν : HasCriticalNu M correlationLength (P.certificate scale).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((P.with_larger_closedBallRadius hradius).certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallRadius_hasCriticalNu P hradius scale hν

/--
[with_larger_closedBallResidual_tableWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_tableWitness_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).tableWitness = P.tableWitness := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_tableWitness P hresidual hbudget

/--
[with_larger_closedBallResidual_closedBallRG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_closedBallRG_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).closedBallRG = P.closedBallRG.with_larger_residual hresidual hbudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_closedBallRG P hresidual hbudget

/--
[with_larger_closedBallResidual_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).closedBallResidual = residual' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_closedBallResidual P hresidual hbudget

/--
[with_larger_closedBallResidual_closedBallRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_closedBallRadius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).closedBallRadius = P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_closedBallRadius P hresidual hbudget

/--
[with_larger_closedBallResidual_closedBallCenter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_closedBallCenter_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).closedBallCenter = P.closedBallCenter := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_closedBallCenter P hresidual hbudget

/--
[with_larger_closedBallResidual_closedBallContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_closedBallContraction_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).closedBallContraction = P.closedBallContraction := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_closedBallContraction P hresidual hbudget

/--
[with_larger_closedBallResidual_closedBallFixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_closedBallFixedPoint_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).closedBallFixedPoint = P.closedBallFixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_closedBallFixedPoint P hresidual hbudget

/--
[with_larger_closedBallResidual_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_tableCertifiedTotalBound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).tableCertifiedTotalBound = P.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_tableCertifiedTotalBound P hresidual hbudget

/--
[with_larger_closedBallResidual_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_tableFiniteBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).tableFiniteBudget = P.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_tableFiniteBudget P hresidual hbudget

/--
[with_larger_closedBallResidual_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_tablePrefixBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).tablePrefixBudget = P.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_tablePrefixBudget P hresidual hbudget

/--
[with_larger_closedBallResidual_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_tailTotalTsum_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).tailTotalTsum = P.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_tailTotalTsum P hresidual hbudget

/--
[with_larger_closedBallResidual_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).tailBudget = P.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_tailBudget P hresidual hbudget

/--
[with_larger_closedBallResidual_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_tailContribution_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).tailContribution = P.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_tailContribution P hresidual hbudget

/--
[with_larger_closedBallResidual_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_certificate_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  (P.with_larger_closedBallResidual hresidual hbudget).certificate scale = P.certificate scale := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_certificate_eq P hresidual hbudget scale

/--
[with_larger_closedBallResidual_certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_certificate_predictedExponent_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius) :
-- imply
  ((P.with_larger_closedBallResidual hresidual hbudget).certificate scale).predictedExponent = (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_certificate_predictedExponent_eq P hresidual hbudget scale

/--
[with_larger_closedBallResidual_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_rgToExponentBridge_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
-- imply
  ((P.with_larger_closedBallResidual hresidual hbudget).certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_rgToExponentBridge P hresidual hbudget scale hbridge

/--
[with_larger_closedBallResidual_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_valid_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
  (hvalid : (P.certificate scale).Valid correlationLength) :
-- imply
  ((P.with_larger_closedBallResidual hresidual hbudget).certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_valid P hresidual hbudget scale hvalid

/--
[with_larger_closedBallResidual_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_larger_closedBallResidual_hasCriticalNu_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {residual' : ℝ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (hresidual : P.closedBallRG.closedBall.residual ≤ residual')
  (hbudget : residual' + P.closedBallRG.closedBall.contraction.c * P.closedBallRG.closedBall.radius ≤ P.closedBallRG.closedBall.radius)
  (hν : HasCriticalNu M correlationLength (P.certificate scale).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((P.with_larger_closedBallResidual hresidual hbudget).certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_larger_closedBallResidual_hasCriticalNu P hresidual hbudget scale hν

/--
[with_tableWitness_as_closedBallResidual_tableWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_tableWitness_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tableWitness = W := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_tableWitness P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_closedBallRG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_closedBallRG_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).closedBallRG = P.closedBallRG.with_larger_residual (by simpa [closedBallResidual] using hresidual) (by simpa [closedBallContraction, closedBallRadius] using hbudget) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_closedBallRG P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).closedBallResidual = W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_closedBallResidual P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_closedBallCenter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_closedBallCenter_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).closedBallCenter = P.closedBallCenter := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_closedBallCenter P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_closedBallRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_closedBallRadius_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).closedBallRadius = P.closedBallRadius := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_closedBallRadius P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_closedBallContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_closedBallContraction_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).closedBallContraction = P.closedBallContraction := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_closedBallContraction P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_closedBallFixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_closedBallFixedPoint_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).closedBallFixedPoint = P.closedBallFixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_closedBallFixedPoint P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tableCertifiedTotalBound = W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_tableFiniteBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tableFiniteBudget = W.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_tableFiniteBudget P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_tablePrefixBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tablePrefixBudget = W.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_tablePrefixBudget P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound_eq_closedBallResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound_eq_closedBallResidual_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tableCertifiedTotalBound = (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).closedBallResidual := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_tableCertifiedTotalBound_eq_closedBallResidual P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_tailTotalTsum_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_tailTotalTsum P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_tailBudget_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tailBudget = W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_tailBudget P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_tailContribution_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_tailContribution P W hresidual hbudget

/--
[with_tableWitness_as_closedBallResidual_certificate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_certificate_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  (P.with_tableWitness_as_closedBallResidual W hresidual hbudget).certificate scale = P.certificate scale := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_certificate_eq P W hresidual hbudget scale

/--
[with_tableWitness_as_closedBallResidual_certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_certificate_predictedExponent_eq_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius) :
-- imply
  ((P.with_tableWitness_as_closedBallResidual W hresidual hbudget).certificate scale).predictedExponent = (P.certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_certificate_predictedExponent_eq P W hresidual hbudget scale

/--
[with_tableWitness_as_closedBallResidual_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_rgToExponentBridge_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius)
  (hbridge : (P.certificate scale).RGToExponentBridge correlationLength) :
-- imply
  ((P.with_tableWitness_as_closedBallResidual W hresidual hbudget).certificate scale).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_rgToExponentBridge P W hresidual hbudget scale hbridge

/--
[with_tableWitness_as_closedBallResidual_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_valid_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius)
  (hvalid : (P.certificate scale).Valid correlationLength) :
-- imply
  ((P.with_tableWitness_as_closedBallResidual W hresidual hbudget).certificate scale).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_valid P W hresidual hbudget scale hvalid

/--
[with_tableWitness_as_closedBallResidual_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailTableClosedBallRGPackage.lean)
-/
@[path]
private lemma with_tableWitness_as_closedBallResidual_hasCriticalNu_eq
  {TailIndex : Type}
  [DecidableEq Case]
  [DecidableEq Coord]
  {M : CriticalModel ι}
  {n : ℕ}
  {scale : BlockScale}
  {correlationLength : ℝ → ℝ}
-- given
  (P : InfiniteTailTableClosedBallRGPackage (Case := Case) (Coord := Coord) (TailIndex := TailIndex) M n)
  (W : InfiniteTailTableWitnessPackage (Case := Case) (α := Coord) M)
  (hresidual : P.closedBallResidual ≤ W.tableCertifiedTotalBound)
  (hbudget : W.tableCertifiedTotalBound + P.closedBallContraction.c * P.closedBallRadius ≤ P.closedBallRadius)
  (hν : HasCriticalNu M correlationLength (P.certificate scale).predictedExponent) :
-- imply
  HasCriticalNu M correlationLength ((P.with_tableWitness_as_closedBallResidual W hresidual hbudget).certificate scale).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailTableClosedBallRGPackage.with_tableWitness_as_closedBallResidual_hasCriticalNu P W hresidual hbudget scale hν


-- created on 2026-10-23
