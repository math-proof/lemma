import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetStability
open StatMech StatMech.FrontierD


/--
[sixVertexContinuousOffsetResidual_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetStability.lean)
-/
@[path]
private lemma sixVertexContinuousOffsetResidual_eq_zero_eq
  {c : Real}
  {f : Real → Real}
  {x : Real}
-- given
  (hf : SixVertexSatisfiesContinuousOffsetEquation c f)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  sixVertexContinuousOffsetResidual c f x = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuousOffsetResidual_eq_zero hf hx

/--
[sixVertexContinuousOffset_error_le_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetStability.lean)
-/
@[path]
private lemma sixVertexContinuousOffset_error_le_residual_eq
  {c : Real}
  {tau f : Real → Real}
  {ε : Real}
-- given
  (hc : 2 < c)
  (htau : Continuous tau)
  (hf : Continuous f)
  (htauOdd : Function.Odd tau)
  (hfOdd : Function.Odd f)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hres : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexContinuousOffsetResidual c f x| ≤ ε) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, := by
-- proof
  apply StatMech.FrontierD.sixVertexContinuousOffset_error_le_residual hc htau hf htauOdd hfOdd htauEq hres

/--
[tendstoUniformlyOn_of_sixVertexContinuousOffsetResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetStability.lean)
-/
@[path]
private lemma tendstoUniformlyOn_of_sixVertexContinuousOffsetResidual_eq
  {c : Real}
  {tau : Real → Real}
  {f : Nat → Real → Real}
  {ε : Nat → Real}
-- given
  (hc : 2 < c)
  (htau : Continuous tau)
  (hf : ∀ n, Continuous (f n))
  (htauOdd : Function.Odd tau)
  (hfOdd : ∀ n, Function.Odd (f n))
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hres : ∀ n x, x ∈ Set.Icc (-Real.pi) Real.pi → |sixVertexContinuousOffsetResidual c (f n) x| ≤ ε n)
  (hεzero : Tendsto ε atTop (nhds 0)) :
-- imply
  TendstoUniformlyOn f tau atTop (Set.Icc (-Real.pi) Real.pi) := by
-- proof
  apply StatMech.FrontierD.tendstoUniformlyOn_of_sixVertexContinuousOffsetResidual hc htau hf htauOdd hfOdd htauEq hres hεzero


-- created on 2026-10-23
