import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
open Finset Matrix StatMech StatMech.FrontierD


/--
[finitePeriodicSucc_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean)
-/
@[path]
private lemma finitePeriodicSucc_castSucc_eq
  {M : ℕ}
  {i : Fin M} :
-- imply
  finitePeriodicSucc (Nat.succ_pos M) i.castSucc = i.succ := by
-- proof
  apply StatMech.FrontierD.finitePeriodicSucc_castSucc i

/--
[finitePeriodicSucc_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean)
-/
@[path]
private lemma finitePeriodicSucc_last_eq
  {M : ℕ} :
-- imply
  finitePeriodicSucc (Nat.succ_pos M) (Fin.last M) = 0 := by
-- proof
  apply StatMech.FrontierD.finitePeriodicSucc_last M

/--
[matrixCompatibleCycleSum_eq_trace_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean)
-/
@[path]
private lemma matrixCompatibleCycleSum_eq_trace_pow_eq
  [Fintype α]
  [DecidableEq α]
  {M : ℕ}
  {A : Matrix α α ℝ}
-- given
  (hM : 0 < M) :
-- imply
  matrixCompatibleCycleSum hM A = Matrix.trace (A ^ M) := by
-- proof
  apply StatMech.FrontierD.matrixCompatibleCycleSum_eq_trace_pow hM A

/--
[sixVertexPeriodicRows_upCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean)
-/
@[path]
private lemma sixVertexPeriodicRows_upCount_eq_eq
  {N M : ℕ}
  {c : ℝ}
  {x : SixVertexPeriodicRows N M hM c}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  sixVertexUpCount (x.1 i) = sixVertexUpCount (x.1 ⟨0, hM⟩) := by
-- proof
  apply StatMech.FrontierD.sixVertexPeriodicRows_upCount_eq hM c x i

/--
[sixVertexPeriodicRowPartitionSum_eq_trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean)
-/
@[path]
private lemma sixVertexPeriodicRowPartitionSum_eq_trace_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hM : 0 < M) :
-- imply
  sixVertexPeriodicRowPartitionSum N M hM c = Matrix.trace (sixVertexTransfer N c ^ M) := by
-- proof
  apply StatMech.FrontierD.sixVertexPeriodicRowPartitionSum_eq_trace N M hM c

/--
[sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean)
-/
@[path]
private lemma sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces_eq
  {N M : ℕ}
  {c : ℝ}
-- given
  (hM : 0 < M) :
-- imply
  sixVertexPeriodicRowPartitionSum N M hM c = ∑ n : Fin (N + 1), Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
-- proof
  apply StatMech.FrontierD.sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces N M hM c

/--
[sixVertexFiniteTorusRowPartitionSum_eq_sum_sector_traces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean)
-/
@[path]
private lemma sixVertexFiniteTorusRowPartitionSum_eq_sum_sector_traces_eq
  {T : EvenTorus}
  {c : ℝ} :
-- imply
  sixVertexFiniteTorusRowPartitionSum T c = ∑ n : Fin (T.width + 1), Matrix.trace (sixVertexSectorTransfer T.width n c ^ T.height) := by
-- proof
  apply StatMech.FrontierD.sixVertexFiniteTorusRowPartitionSum_eq_sum_sector_traces T c


-- created on 2026-10-23
