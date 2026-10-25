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
import Theorem.Analysis.NormedSpace.Geometric.Part6


section

open Set

namespace FunctionalAnalysis.GeometricWanted

noncomputable def frac (y : ℝ) : ℝ :=
  if hi y = lo y then 0 else (y - lo y) / (hi y - lo y)

noncomputable def gval (f : C(cantorSet, ℝ)) (y : ℝ) : ℝ :=
  Fext f (lo y) + (Fext f (hi y) - Fext f (lo y)) * frac y

end FunctionalAnalysis.GeometricWanted
end
