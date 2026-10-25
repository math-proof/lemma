import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.BornologyProposition
open Set BornologyProp


namespace BornologyProp

/--
[setOrbit_bounded_of_pointOrbit_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyProposition.lean)
-/
@[path]
lemma setOrbit_bounded_of_pointOrbit_bounded
  [PseudoMetricSpace X]
  {act : G → X → X}
  {E : Set G}
  {x : X}
  {Y : Set X}
-- given
  (hiso : ∀ g : G, ∀ a b : X, dist (act g a) (act g b) = dist a b)
  (hEx : Bornology.IsBounded (pointOrbit act E x))
  (hY : Bornology.IsBounded Y) :
-- imply
  Bornology.IsBounded (setOrbit act E Y) := by
-- proof
  rw [Metric.isBounded_iff_subset_closedBall x] at hEx hY ⊢
  obtain ⟨δ, hδ⟩ := hEx
  obtain ⟨D, hD⟩ := hY
  refine ⟨δ + D, fun z hz => ?_⟩
  obtain ⟨g, hg, y, hy, rfl⟩ := hz
  have h1 : dist (act g x) x ≤ δ := hδ ⟨g, hg, rfl⟩
  have h2 : dist y x ≤ D := hD hy
  simp only [Metric.mem_closedBall]
  calc dist (act g y) x
    ≤ dist (act g y) (act g x) + dist (act g x) x := dist_triangle _ _ _
    _ = dist y x + dist (act g x) x := by rw [hiso g y x]
    _ ≤ D + δ := by linarith
    _ = δ + D := by ring
/-- Empty.Finite Bruhat coverage of $E$ implies the existence of a point with bounded orbit. -/
variable [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx} {Ω : Type*}
/-- Main proposition (Section 17.7): $E$ is generalized BN-pair bounded $\iff$ some point orbit is
bounded $\land$ every set orbit of a bounded set is bounded. -/

end BornologyProp


-- created on 2026-10-23
