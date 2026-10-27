import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
open Metric Set Topology StatMech StatMech.FrontierA


/--
[holomorphicFamily_equicontinuousOn_of_compactBounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HolomorphicFamilyEquicontinuity.lean)
-/
@[path]
private lemma holomorphicFamily_equicontinuousOn_of_compactBounded_eq
  {F : ι → ℂ → ℂ}
  {U : Set ℂ}
-- given
  (hU : IsOpen U)
  (hF : ∀ i, DifferentiableOn ℂ (F i) U)
  (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ i z, z ∈ K → ‖F i z‖ ≤ C) :
-- imply
  ∀ K : Set ℂ, IsCompact K → K ⊆ U → EquicontinuousOn F K := by
-- proof
  apply StatMech.FrontierA.holomorphicFamily_equicontinuousOn_of_compactBounded F U hU hF hbounded

/--
[holomorphicFamily_restrictionClosure_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HolomorphicFamilyEquicontinuity.lean)
-/
@[path]
private lemma holomorphicFamily_restrictionClosure_compact_eq
  {F : ι → ℂ → ℂ}
  {U : Set ℂ}
  {K : Set ℂ}
-- given
  (hU : IsOpen U)
  (hF : ∀ i, DifferentiableOn ℂ (F i) U)
  (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ i z, z ∈ K → ‖F i z‖ ≤ C)
  (hK : IsCompact K)
  (hKU : K ⊆ U) :
-- imply
  IsCompact (closure (Set.range (fun i => UniformFun.ofFun (fun z : K => F i z)))) := by
-- proof
  apply StatMech.FrontierA.holomorphicFamily_restrictionClosure_compact F U hU hF hbounded K hK hKU

/--
[holomorphicFamily_uniformSubsequenceOn_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/HolomorphicFamilyEquicontinuity.lean)
-/
@[path]
private lemma holomorphicFamily_uniformSubsequenceOn_compact_eq
  {F : ι → ℂ → ℂ}
  {U : Set ℂ}
  {K : Set ℂ}
  {u : ℕ → ι}
-- given
  (hU : IsOpen U)
  (hF : ∀ i, DifferentiableOn ℂ (F i) U)
  (hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ i z, z ∈ K → ‖F i z‖ ≤ C)
  (hK : IsCompact K)
  (hKU : K ⊆ U) :
-- imply
  ∃ (g : K → ℂ) (ψ : ℕ → ℕ), StrictMono ψ ∧ TendstoUniformly (fun n (z : K) => F (u (ψ n)) z) g Filter.atTop := by
-- proof
  apply StatMech.FrontierA.holomorphicFamily_uniformSubsequenceOn_compact F U hU hF hbounded K hK hKU u


-- created on 2026-10-23
