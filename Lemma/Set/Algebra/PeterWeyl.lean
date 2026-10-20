import Mathlib
import sympy.Basic
import sympy.atlas.Topology.Algebra.PeterWeyl
open MeasureTheory
open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction
open MathlibExt.Topology.Algebra.PeterWeylWanted


/--
[peter_weyl_point_separation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean)
-/
@[path]
private lemma peter_weyl_point_separation_eq
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  {x y : G}
-- given
  (hxy : x ≠ y) :
-- imply
  ∃ (n : ℕ) (_hn : 0 < n) (ρ : G → Matrix (Fin n) (Fin n) ℂ),
    Continuous ρ ∧
    ρ 1 = 1 ∧
    (∀ g h : G, ρ (g * h) = ρ g * ρ h) ∧
    (∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ) ∧
    ρ x ≠ ρ y := by
-- proof
  apply MathlibExt.Topology.Algebra.PeterWeylWanted.peter_weyl_point_separation hxy


-- created on 2026-10-20
