import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCaccioppoli
open StatMech StatMech.Universality


/--
[isingFiniteGraphDartSum_eq_sum_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean)
-/
@[path]
private lemma isingFiniteGraphDartSum_eq_sum_laplacian_eq
  [Fintype V]
  {G : SimpleGraph V}
  {w u : V → Real} :
-- imply
  isingFiniteGraphDartSum G (fun x y ↦ w x * (u y - u x)) = ∑ x, w x * isingFiniteGraphLaplacian G u x := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDartSum_eq_sum_laplacian G w u

/--
[isingFiniteGraphDartSum_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean)
-/
@[path]
private lemma isingFiniteGraphDartSum_swap_eq
  [Fintype V]
  {G : SimpleGraph V}
  {F : V → V → Real} :
-- imply
  isingFiniteGraphDartSum G (fun x y ↦ F y x) = isingFiniteGraphDartSum G F := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDartSum_swap G F

/--
[isingFiniteGraphDartSum_cutoff_integrationByParts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean)
-/
@[path]
private lemma isingFiniteGraphDartSum_cutoff_integrationByParts_eq
  [Fintype V]
  {G : SimpleGraph V}
  {eta u : V → Real} :
-- imply
  2 * isingFiniteGraphDartSum G (fun x y ↦ eta x ^ 2 * u x * (u y - u x)) = -isingFiniteGraphDartSum G (fun x y ↦ (eta y ^ 2 * u y - eta x ^ 2 * u x) * (u y - u x)) := by
-- proof
  apply StatMech.Universality.isingFiniteGraphDartSum_cutoff_integrationByParts G eta u

/--
[isingFiniteGraph_caccioppoli_of_weighted_subharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean)
-/
@[path]
private lemma isingFiniteGraph_caccioppoli_of_weighted_subharmonic_eq
  [Fintype V]
  {G : SimpleGraph V}
  {eta u : V → Real}
  {M : Real}
-- given
  (hu0 : ∀ x, 0 ≤ u x)
  (huM : ∀ x, u x ≤ M)
  (hweighted : 0 ≤ isingFiniteGraphDartSum G (fun x y ↦ eta x ^ 2 * u x * (u y - u x))) :
-- imply
  isingFiniteGraphDartSum G (fun x y ↦ (eta y * u y - eta x * u x) ^ 2) ≤ M ^ 2 * isingFiniteGraphDartSum G (fun x y ↦ (eta y - eta x) ^ 2) := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_caccioppoli_of_weighted_subharmonic G eta u M hu0 huM hweighted

/--
[isingFiniteGraph_caccioppoli_of_subharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean)
-/
@[path]
private lemma isingFiniteGraph_caccioppoli_of_subharmonicOn_eq
  [Fintype V]
  {G : SimpleGraph V}
  {eta u : V → Real}
  {lower upper : Real}
-- given
  (boundary : V → Prop)
  (hsub : IsingFiniteGraphSubharmonicOn G boundary u)
  (hlower : ∀ x, lower ≤ u x)
  (hupper : ∀ x, u x ≤ upper)
  (hsupport : ∀ x, eta x ≠ 0 → ¬ boundary x) :
-- imply
  isingFiniteGraphDartSum G (fun x y ↦ (eta y * (u y - lower) - eta x * (u x - lower)) ^ 2) ≤ (upper - lower) ^ 2 * isingFiniteGraphDartSum G (fun x y ↦ (eta y - eta x) ^ 2) := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_caccioppoli_of_subharmonicOn G boundary eta u lower upper hsub hlower hupper hsupport

/--
[isingFiniteGraph_caccioppoli_of_superharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean)
-/
@[path]
private lemma isingFiniteGraph_caccioppoli_of_superharmonicOn_eq
  [Fintype V]
  {G : SimpleGraph V}
  {eta u : V → Real}
  {lower upper : Real}
-- given
  (boundary : V → Prop)
  (hsuper : IsingFiniteGraphSuperharmonicOn G boundary u)
  (hlower : ∀ x, lower ≤ u x)
  (hupper : ∀ x, u x ≤ upper)
  (hsupport : ∀ x, eta x ≠ 0 → ¬ boundary x) :
-- imply
  isingFiniteGraphDartSum G (fun x y ↦ (eta y * (upper - u y) - eta x * (upper - u x)) ^ 2) ≤ (upper - lower) ^ 2 * isingFiniteGraphDartSum G (fun x y ↦ (eta y - eta x) ^ 2) := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_caccioppoli_of_superharmonicOn G boundary eta u lower upper hsuper hlower hupper hsupport

/--
[isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean)
-/
@[path]
private lemma isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn_eq
  [Fintype V]
  {G : SimpleGraph V}
  {eta u : V → Real}
  {lower upper c E : Real}
  {S : Finset G.Dart}
-- given
  (boundary : V → Prop)
  (hsub : IsingFiniteGraphSubharmonicOn G boundary u)
  (hlower : ∀ x, lower ≤ u x)
  (hupper : ∀ x, u x ≤ upper)
  (hsupport : ∀ x, eta x ≠ 0 → ¬ boundary x)
  (hc : 0 ≤ c)
  (heta : ∀ d ∈ S, c ≤ eta d.snd)
  (hcutoff : isingFiniteGraphDartSum G (fun x y ↦ (eta y - eta x) ^ 2) ≤ E) :
-- imply
  c ^ 2 * (∑ d ∈ S, |u d.snd - u d.fst|) ^ 2 ≤ 4 * (#S : Real) * (upper - lower) ^ 2 * E := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn G boundary eta u lower upper c E S hsub hlower hupper hsupport hc heta hcutoff

/--
[isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteCaccioppoli.lean)
-/
@[path]
private lemma isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn_eq
  [Fintype V]
  {G : SimpleGraph V}
  {eta u : V → Real}
  {lower upper c E : Real}
  {S : Finset G.Dart}
-- given
  (boundary : V → Prop)
  (hsuper : IsingFiniteGraphSuperharmonicOn G boundary u)
  (hlower : ∀ x, lower ≤ u x)
  (hupper : ∀ x, u x ≤ upper)
  (hsupport : ∀ x, eta x ≠ 0 → ¬ boundary x)
  (hc : 0 ≤ c)
  (heta : ∀ d ∈ S, c ≤ eta d.snd)
  (hcutoff : isingFiniteGraphDartSum G (fun x y ↦ (eta y - eta x) ^ 2) ≤ E) :
-- imply
  c ^ 2 * (∑ d ∈ S, |u d.snd - u d.fst|) ^ 2 ≤ 4 * (#S : Real) * (upper - lower) ^ 2 * E := by
-- proof
  apply StatMech.Universality.isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn G boundary eta u lower upper c E S hsuper hlower hupper hsupport hc heta hcutoff


-- created on 2026-10-23
