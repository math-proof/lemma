import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.HeckeAlgebra.Generalized.Part3
open GeneralizedHecke GeneralizedHecke.OmegaConvolutionData GeneralizedHecke.HeckeConvolutionIdentities


namespace Definitions
end Definitions
namespace GeneralizedHecke

/--
[GeneralizedBNPairData.borelInLabelPreserving_holds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean)
-/
@[path]
private lemma GeneralizedBNPairData.borelInLabelPreserving_holds
  [Group G]
  {d : GeneralizedBNPairData G} :
-- imply
  d.BorelInLabelPreserving :=
-- proof
  d.borel_in_labelPreserving

end GeneralizedHecke

namespace GeneralizedHecke

/--
[GeneralizedBNPairData.normalizerRestrictedIsIntersection_holds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean)
-/
@[path]
private lemma GeneralizedBNPairData.normalizerRestrictedIsIntersection_holds
  [Group G]
  {d : GeneralizedBNPairData G} :
-- imply
  d.NormalizerRestrictedIsIntersection := by
-- proof
  intro g
  rwa [d.normalizerRestricted_eq]

end GeneralizedHecke

namespace GeneralizedHecke

/--
[GeneralizedBNPairData.torusIsIntersection_holds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean)
-/
@[path]
private lemma GeneralizedBNPairData.torusIsIntersection_holds
  [Group G]
  {d : GeneralizedBNPairData G} :
-- imply
  d.TorusIsIntersection := by
-- proof
  intro g
  rwa [d.torus_eq]

end GeneralizedHecke

namespace GeneralizedHecke

/--
[GeneralizedBNPairData.torusRestrictedIsIntersection_holds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean)
-/
@[path]
private lemma GeneralizedBNPairData.torusRestrictedIsIntersection_holds
  [Group G]
  {d : GeneralizedBNPairData G} :
-- imply
  d.TorusRestrictedIsIntersection := by
-- proof
  intro g
  rwa [d.torusRestricted_eq]

end GeneralizedHecke

namespace GeneralizedHecke

/--
[biInvariant_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean)
-/
@[path]
private lemma biInvariant_const
  [Group G]
  {B : Subgroup G}
  {c : R} :
-- imply
  BiInvariantFunction B (fun _ : G => c) :=
-- proof
  fun _ _ _ _ _ => rfl
universe u

end GeneralizedHecke

namespace GeneralizedHecke.OmegaConvolutionData

/--
[algHomToH_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean)
-/
@[path]
private lemma algHomToH_injective
  {k : Type u}
  [CommRing k]
  {Ω : Type u}
  [Group Ω]
  {d : OmegaConvolutionData k Ω} :
-- imply
  Function.Injective d.algHomToH := by
-- proof
  intro x y hxy
  suffices h : ∀ (a : MonoidAlgebra k Ω), d.algHomToH a = 0 → a = 0 by
    have := h (x - y) (by rw [map_sub]; exact sub_eq_zero.mpr hxy)
    exact sub_eq_zero.mp this
  intro a ha
  have hli := d.ch_linearIndependent
  rw [linearIndependent_iff] at hli
  apply hli
  rw [Finsupp.linearCombination_apply]
  simp only [algHomToH, MonoidAlgebra.lift_apply, chMonoidHom] at ha
  exact ha

end GeneralizedHecke.OmegaConvolutionData

namespace GeneralizedHecke.HeckeConvolutionIdentities

/--
[commutation_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean)
-/
@[path]
private lemma commutation_relation
  {k : Type u}
  [CommRing k]
  {Ω : Type u}
  [Group Ω]
  {W : Type u}
  [Group W]
  {d : HeckeConvolutionIdentities k Ω W}
  {σ : Ω}
  {w : W} :
-- imply
  d.ch_weyl w * d.ch_omega σ = d.ch_omega σ * d.ch_weyl (d.omegaConj σ w) := by
-- proof
  rw [d.conv_right w σ, ← d.conv_left σ (d.omegaConj σ w)]

end GeneralizedHecke.HeckeConvolutionIdentities

namespace GeneralizedHecke.HeckeConvolutionIdentities

/--
[ch_full_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generalized.lean)
-/
@[path]
private lemma ch_full_factorization
  {k : Type u}
  [CommRing k]
  {Ω : Type u}
  [Group Ω]
  {W : Type u}
  [Group W]
  {d : HeckeConvolutionIdentities k Ω W}
  {σ : Ω}
  {w : W} :
-- imply
  d.ch_full σ w = d.ch_omega σ * d.ch_weyl w :=
-- proof
  (d.conv_left σ w).symm


-- created on 2026-10-24
