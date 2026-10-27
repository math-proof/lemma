import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityComponent
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertex_stabilityGauge_lt_eq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityComponent.lean)
-/
@[path]
private lemma sixVertex_stabilityGauge_lt_eq_le_eq
  [TopologicalSpace X]
  {g : X → Real}
  {inner outer : Real}
-- given
  (hio : inner < outer)
  (hgap : ∀ x, ¬(inner < g x ∧ g x < outer)) :
-- imply
  {x | g x < outer} = {x | g x ≤ inner} := by
-- proof
  apply StatMech.FrontierD.sixVertex_stabilityGauge_lt_eq_le g hio hgap

/--
[exists_sixVertexContinuousEvenSymmetricBetheBranch_of_stabilityGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityComponent.lean)
-/
@[path]
private lemma exists_sixVertexContinuousEvenSymmetricBetheBranch_of_stabilityGauge_eq
  {a b c₀ : Real}
  {N m : Nat}
  {g : SixVertexBetheContinuationSpace a b N (m + m) → Real}
  {inner outer : Real}
  {z₀ : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * (m + m) ≤ N)
  (hg : Continuous g)
  (hio : inner < outer)
  (hgap : ∀ z, ¬(inner < g z ∧ g z < outer))
  (hjac : ∀ z, g z < outer → Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1 (sixVertexEvenPositiveHalfProjection m z.1.2)))
  (hz₀g : g z₀ < outer)
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin (m + m) → Real), roots c₀ = z₀.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousEvenSymmetricBetheBranch_of_stabilityGauge ha hab hc₀ hN hhalf g hg hio hgap hjac z₀ hz₀g hz₀


-- created on 2026-10-23
