import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronRootSheet
open Filter Topology StatMech StatMech.FrontierD


/--
[eventuallyEq_sixVertexSectorTopEigenvalue_of_characteristicRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronRootSheet.lean)
-/
@[path]
private lemma eventuallyEq_sixVertexSectorTopEigenvalue_of_characteristicRoot_eq
  {N n : Nat}
  {c : Real}
  {f : Real → Real}
-- given
  (hn : n ≤ N)
  (hc : 0 < c)
  (hf : ContinuousAt f c)
  (hfc : f c = sixVertexSectorTopEigenvalue N n hn c)
  (hroot : ∀ᶠ t : Real in nhds c, Matrix.det (f t • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) - sixVertexSectorTransfer N n t) = 0) :
-- imply
  f =ᶠ[nhds c] sixVertexSectorTopEigenvalue N n hn := by
-- proof
  apply StatMech.FrontierD.eventuallyEq_sixVertexSectorTopEigenvalue_of_characteristicRoot hn hc hf hfc hroot

/--
[sixVertexSectorTopEigenvalue_eqOn_of_analytic_characteristicRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronRootSheet.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_eqOn_of_analytic_characteristicRoot_eq
  {N n : Nat}
  {U : Set Real}
  {c : Real}
  {f : Real → Real}
-- given
  (hn : n ≤ N)
  (hU : IsPreconnected U)
  (hUopen : IsOpen U)
  (hUpos : U ⊆ Set.Ioi 0)
  (hcU : c ∈ U)
  (hc : 0 < c)
  (hf : AnalyticOnNhd Real f U)
  (hroot : ∀ t ∈ U, Matrix.det (f t • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) - sixVertexSectorTransfer N n t) = 0)
  (hfc : f c = sixVertexSectorTopEigenvalue N n hn c) :
-- imply
  Set.EqOn f (sixVertexSectorTopEigenvalue N n hn) U := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_eqOn_of_analytic_characteristicRoot hn hU hUopen hUpos hcU hc hf hroot hfc


-- created on 2026-10-23
