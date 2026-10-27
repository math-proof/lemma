import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology


namespace MetaMathlibExt

noncomputable def Aterm (x : ℝ) (n : ℕ) : ℝ :=
  (2*x)^(2*n)/((n : ℝ)*(Nat.choose (2*n) n : ℝ))

noncomputable def Sfun (x : ℝ) : ℝ := ∑' n, Aterm x n

end MetaMathlibExt
