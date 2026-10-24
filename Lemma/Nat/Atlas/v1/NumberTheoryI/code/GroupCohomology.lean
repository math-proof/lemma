import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.GroupCohomology
open CategoryTheory GroupCohomology ChainHomotopy HomotopyHomology DerivedFunctor LongExactDerived CochainHomotopyCohomology Resolution HomFunctorHomotopy
open CategoryTheory.Limits CategoryTheory.ShortComplex
open CategoryTheory HomologicalComplex


namespace GroupCohomology

/--
[coboundaryMap_comp_coboundaryMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma coboundaryMap_comp_coboundaryMap
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {A : Rep k G}
  {n : ℕ} :
-- imply
  coboundaryMap A n ≫ coboundaryMap A (n + 1) = 0 :=
-- proof
(groupCohomology.inhomogeneousCochains A).d_comp_d n (n + 1) (n + 2)

end GroupCohomology

namespace GroupCohomology

/--
[ses_cochains_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma ses_cochains_exact
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {X : CategoryTheory.ShortComplex (Rep k G)}
-- given
  (hX : X.ShortExact) :
-- imply
  (X.map (groupCohomology.cochainsFunctor k G)).ShortExact :=
-- proof
  groupCohomology.map_cochainsFunctor_shortExact hX

end GroupCohomology

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]
/--
[long_exact_sequence_exact₂](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma long_exact_sequence_exact₂
  {X : CategoryTheory.ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ) :
  (groupCohomology.mapShortComplex₂ X n).Exact :=
  groupCohomology.mapShortComplex₂_exact hX n

end GroupCohomology

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]
/--
[long_exact_sequence_exact₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma long_exact_sequence_exact₁
  {X : CategoryTheory.ShortComplex (Rep k G)} (hX : X.ShortExact)
  {i j : ℕ} (hij : i + 1 = j) :
  (groupCohomology.mapShortComplex₁ hX hij).Exact :=
  groupCohomology.mapShortComplex₁_exact hX hij
end GroupCohomology
namespace DeltaFunctor
open CategoryTheory
universe w₁ w₂
variable (𝒜 : Type w₁) [Category.{w₂} 𝒜] [Abelian 𝒜]
  (ℬ : Type w₁) [Category.{w₂} ℬ] [Abelian ℬ]


namespace GroupCohomology

/--
[cohomology_coinduced_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma cohomology_coinduced_vanishing
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {A : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {n : ℕ} :
-- imply
  Limits.IsZero (groupCohomology (Rep.coind.{u, u, u, u} (⊥ : Subgroup G).subtype A) (n + 1)) := by
-- proof
  haveI : Subsingleton ↥(⊥ : Subgroup G) := Unique.instSubsingleton
  exact (isZero_groupCohomology_succ_of_subsingleton A n).of_iso
    (groupCohomology.coindIso A (n + 1))

end GroupCohomology

namespace GroupCohomology

/--
[homology_map_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma homology_map_id
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {A : Rep k G}
  {n : ℕ} :
-- imply
  homology_map (𝟙 A) n = 𝟙 (HomologyGroup A n) :=
-- proof
  groupHomology.map_id n

end GroupCohomology

namespace GroupCohomology

/--
[homology_map_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma homology_map_comp
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {A B C : Rep k G}
  {φ : A ⟶ B}
  {ψ : B ⟶ C}
  {n : ℕ} :
-- imply
  homology_map (φ ≫ ψ) n = homology_map φ n ≫ homology_map ψ n :=
-- proof
  groupHomology.map_id_comp φ ψ n

end GroupCohomology

namespace ChainHomotopy

/--
[homotopicChainMaps_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma homotopicChainMaps_refl
  {R : Type v}
  [Ring R]
  {C D : ChainComplexDef.ChainComplexRMod R}
  {f : C ⟶ D} :
-- imply
  HomotopicChainMaps f f :=
-- proof
  ⟨Homotopy.refl f⟩

end ChainHomotopy

namespace ChainHomotopy

/--
[homotopicChainMaps_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma homotopicChainMaps_symm
  {R : Type v}
  [Ring R]
  {C D : ChainComplexDef.ChainComplexRMod R}
  {f g : C ⟶ D}
-- given
  (h : HomotopicChainMaps f g) :
-- imply
  HomotopicChainMaps g f :=
-- proof
  h.map Homotopy.symm

end ChainHomotopy

namespace ChainHomotopy

/--
[homotopicChainMaps_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma homotopicChainMaps_trans
  {R : Type v}
  [Ring R]
  {C D : ChainComplexDef.ChainComplexRMod R}
  {f₁ f₂ f₃ : C ⟶ D}
-- given
  (h₁ : HomotopicChainMaps f₁ f₂)
  (h₂ : HomotopicChainMaps f₂ f₃) :
-- imply
  HomotopicChainMaps f₁ f₃ := by
-- proof
  obtain ⟨h₁⟩ := h₁
  obtain ⟨h₂⟩ := h₂
  exact ⟨h₁.trans h₂⟩
end ChainHomotopy
namespace HomotopyHomology
open CategoryTheory
universe v


namespace HomotopyHomology

/--
[homotopic_chain_maps_induce_equal_homology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma homotopic_chain_maps_induce_equal_homology
  {R : Type v}
  [Ring R]
  {C D : ChainComplexDef.ChainComplexRMod R}
  {f g : C ⟶ D}
  {n : ℕ}
-- given
  (h : Homotopy f g) :
-- imply
  (ChainComplexDef.chainHomologyFunctor R n).map f = (ChainComplexDef.chainHomologyFunctor R n).map g :=
-- proof
  h.homologyMap_eq n
end HomotopyHomology
namespace DerivedFunctor
open CategoryTheory
universe v

end HomotopyHomology

namespace DerivedFunctor

/--
[coboundaryMap_comp_coboundaryMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma coboundaryMap_comp_coboundaryMap
  {R : Type v}
  [Ring R]
  {C : CochainComplexRMod R}
  {n : ℕ} :
-- imply
  coboundaryMap C n ≫ coboundaryMap C (n + 1) = 0 :=
-- proof
  C.d_comp_d n (n + 1) (n + 2)

end DerivedFunctor

namespace LongExactDerived

/--
[cochainLES_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma cochainLES_exact
  {R : Type v}
  [Ring R]
  {S : ShortComplex (DerivedFunctor.CochainComplexRMod R)}
  {n : ℕ}
-- given
  (hS : S.ShortExact) :
-- imply
  (HomologicalComplex.HomologySequence.composableArrows₅ hS n (n + 1) rfl).Exact :=
-- proof
  HomologicalComplex.HomologySequence.composableArrows₅_exact hS n (n + 1) rfl
end LongExactDerived
namespace CochainHomotopyCohomology
open CategoryTheory
universe v


namespace CochainHomotopyCohomology

/--
[homotopic_cochain_maps_cohomology_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma homotopic_cochain_maps_cohomology_eq
  {R : Type v}
  [Ring R]
  {C D : DerivedFunctor.CochainComplexRMod R}
  {f g : C ⟶ D}
  {n : ℕ}
-- given
  (h : Homotopy f g) :
-- imply
  HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n :=
-- proof
  h.homologyMap_eq n
end CochainHomotopyCohomology
namespace Resolution
open CategoryTheory
universe v

end CochainHomotopyCohomology

namespace Resolution

/--
[ProjectiveResolutionRMod.exactAt_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma ProjectiveResolutionRMod.exactAt_succ
  {R : Type v}
  [Ring R]
  {M : ModuleCat.{v} R}
  {P : ProjectiveResolutionRMod M}
  {n : ℕ} :
-- imply
  P.complex.ExactAt (n + 1) :=
-- proof
  P.complex_exactAt_succ n

end Resolution

namespace Resolution

/--
[InjectiveResolutionRMod.exactAt_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma InjectiveResolutionRMod.exactAt_succ
  {R : Type v}
  [Ring R]
  {M : ModuleCat.{v} R}
  {I : InjectiveResolutionRMod M}
  {n : ℕ} :
-- imply
  I.cocomplex.ExactAt (n + 1) :=
-- proof
  I.cocomplex_exactAt_succ n
end Resolution
namespace HomFunctorHomotopy
open CategoryTheory HomologicalComplex
universe v


namespace HomFunctorHomotopy

/--
[hom_functor_preserves_homotopy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
lemma hom_functor_preserves_homotopy
  {R : Type v}
  [Ring R]
  {A : ModuleCat.{v} R}
  {C D : ChainComplexDef.ChainComplexRMod R}
  {f g : C ⟶ D}
-- given
  (hfg : Nonempty (Homotopy f g)) :
-- imply
  Nonempty (Homotopy ((homStarFunctor A).map f.op) ((homStarFunctor A).map g.op)) :=
-- proof
  hfg.map (fun h => Functor.mapHomotopy (preadditiveYoneda.obj A) (homotopyOp h))

end HomFunctorHomotopy

/--
[long_exact_sequence_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
private lemma long_exact_sequence_exact_eq
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {X : CategoryTheory.ShortComplex (Rep k G)}
  {n : ℕ}
-- given
  (hX : X.ShortExact) :
-- imply
  (groupCohomology.mapShortComplex₂ X n).Exact := by
-- proof
  apply GroupCohomology.long_exact_sequence_exact hX n

/--
[long_exact_sequence_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean)
-/
@[path]
private lemma long_exact_sequence_exact_eq_2
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {X : CategoryTheory.ShortComplex (Rep k G)}
  {i j : ℕ}
-- given
  (hX : X.ShortExact)
  (hij : i + 1 = j) :
-- imply
  (groupCohomology.mapShortComplex₁ hX hij).Exact := by
-- proof
  apply GroupCohomology.long_exact_sequence_exact hX hij


-- created on 2026-10-23
