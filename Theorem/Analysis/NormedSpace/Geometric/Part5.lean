import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Separation.CompletelyRegular
import Def.Analysis.NormedSpace.Geometric.Part4


section

open Set

namespace FunctionalAnalysis.GeometricWanted

theorem Slo_bddAbove {y : ℝ} : BddAbove (cantorSet ∩ Iic y) :=
  ⟨1, fun _ hs => (cantor_subset hs.1).2⟩

theorem Shi_bddBelow {y : ℝ} : BddBelow (cantorSet ∩ Ici y) :=
  ⟨0, fun _ hs => (cantor_subset hs.1).1⟩

theorem lo_mem {y : ℝ} (hy : 0 ≤ y) : lo y ∈ cantorSet ∩ Iic y :=
  (isClosed_cantorSet.inter isClosed_Iic).csSup_mem ⟨0, zero_mem_cantorSet, hy⟩ Slo_bddAbove

theorem hi_mem {y : ℝ} (hy : y ≤ 1) : hi y ∈ cantorSet ∩ Ici y :=
  (isClosed_cantorSet.inter isClosed_Ici).csInf_mem ⟨1, one_mem_cantorSet, hy⟩ Shi_bddBelow

theorem lo_cantor {y : ℝ} (hy : 0 ≤ y) : lo y ∈ cantorSet := (lo_mem hy).1

theorem lo_le {y : ℝ} (hy : 0 ≤ y) : lo y ≤ y := (lo_mem hy).2

theorem hi_cantor {y : ℝ} (hy : y ≤ 1) : hi y ∈ cantorSet := (hi_mem hy).1

theorem le_hi {y : ℝ} (hy : y ≤ 1) : y ≤ hi y := (hi_mem hy).2

theorem le_lo {y s : ℝ} (hs : s ∈ cantorSet) (hsy : s ≤ y) : s ≤ lo y :=
  le_csSup Slo_bddAbove ⟨hs, hsy⟩

theorem hi_le {y s : ℝ} (hs : s ∈ cantorSet) (hys : y ≤ s) : hi y ≤ s :=
  csInf_le Shi_bddBelow ⟨hs, hys⟩

theorem lo_le_hi {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : lo y ≤ hi y :=
  le_trans (lo_le hy0) (le_hi hy1)

theorem lo_eq_self {s : ℝ} (hs : s ∈ cantorSet) : lo s = s :=
  le_antisymm (lo_le (cantor_subset hs).1) (le_lo hs le_rfl)

theorem hi_eq_self {s : ℝ} (hs : s ∈ cantorSet) : hi s = s :=
  le_antisymm (hi_le hs le_rfl) (le_hi (cantor_subset hs).2)

end FunctionalAnalysis.GeometricWanted
end
