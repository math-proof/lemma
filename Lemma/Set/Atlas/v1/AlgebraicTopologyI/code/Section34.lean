import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology CechCohomology CapProduct
open subsets `members ⊂ Opens Y` whose union is all of `Y`. The set of


namespace CapProduct

/--
[cap_product_restriction_commutes_abstract](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean)
-/
@[path]
lemma cap_product_restriction_commutes_abstract
  {R : Type}
  [CommRing R]
  [TopologicalSpace X]
  {K U V : Set X}
  {pairU : CapProductPairingOf R U K hU (hKV.trans hVU)}
  {pairV : CapProductPairingOf R V K hV hKV}
  {ι : ProjectionFormula R pairV.toCapProductPairing pairU.toCapProductPairing}
  {exc : ExcisionData R hK hVU pairU.toCapProductPairing pairV.toCapProductPairing}
  {b : pairU.CohomGrp}
  {x : pairU.RelHomGrpN}
-- given
  (hK : IsClosed K)
  (hU : IsOpen U)
  (hV : IsOpen V)
  (hKV : K ⊆ V)
  (hVU : V ⊆ U)
  (hexcN : Function.RightInverse exc.excInvN ι.pushforwardN)
  (hexcQ : Function.LeftInverse exc.excInvQ ι.pushforwardQ) :
-- imply
  exc.excInvQ (pairU.cap b x) = pairV.cap (ι.pullback b) (exc.excInvN x) := by
-- proof
  have h_push_inv : ι.pushforwardN (exc.excInvN x) = x := hexcN x
  have h_proj := ι.formula b (exc.excInvN x)
  rw [h_push_inv] at h_proj
  rw [← h_proj]
  exact hexcQ _

end CapProduct

/--
[cech_cohomology_iso_of_regular_neighborhood_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean)
-/
@[path]
private lemma cech_cohomology_iso_of_regular_neighborhood_condition_eq
  [CommRing R]
  [Preorder ι]
  [DecidableEq ι]
  {G : ι → Type*}
  [∀ i, AddCommGroup (G i)]
  [∀ i, Module R (G i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
  [DirectedSystem G (f · · ·)]
  [IsDirectedOrder ι]
  [Nonempty ι]
  [AddCommGroup P]
  [Module R P]
-- given
  (g : ∀ i, G i →ₗ[R] P)
  (hg : ∀ i j hij x, g j (f i j hij x) = g i x)
  (hreg : RegularNeighborhoodCondition g) :
-- imply
  Function.Bijective (Module.DirectLimit.lift R ι G f g hg) := by
-- proof
  apply CechCohomology.cech_cohomology_iso_of_regular_neighborhood_condition g hg hreg

/--
[topological_cech_cohomology_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean)
-/
@[path]
private lemma topological_cech_cohomology_iso_eq
  [TopologicalSpace X]
  {K : Set X}
  [CommRing R]
  [DecidableEq (OpenNeighborhoods K)]
  {H : OpenNeighborhoods K → Type*}
  [∀ U, AddCommGroup (H U)]
  [∀ U, Module R (H U)]
  {ρ : ∀ U V : OpenNeighborhoods K, U ≤ V → H U →ₗ[R] H V}
  [DirectedSystem H (ρ · · ·)]
  [AddCommGroup P]
  [Module R P]
-- given
  (_hK : IsClosed K)
  (g : ∀ U : OpenNeighborhoods K, H U →ₗ[R] P)
  (hcompat : ∀ U V (h : U ≤ V) x, g V (ρ U V h x) = g U x)
  (hreg : TopologicalRegularNeighborhoodCondition g) :
-- imply
  Function.Bijective (Module.DirectLimit.lift R (OpenNeighborhoods K) H ρ g hcompat) := by
-- proof
  apply CechCohomology.topological_cech_cohomology_iso _hK g hcompat hreg


-- created on 2026-10-23
