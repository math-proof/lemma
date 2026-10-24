import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section5
open CategoryTheory HomotopyInvariance HomotopyTheory
open ContinuousMap unitInterval
open ContinuousMap
open CategoryTheory HomologicalComplex
open CategoryTheory AlgebraicTopology HomologicalComplex Limits
open unitInterval ContinuousMap
open CategoryTheory Limits AlgebraicTopology HomologicalComplex


namespace HomotopyInvariance

/--
[homotopy_invariance_of_homology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean)
-/
@[path]
lemma homotopy_invariance_of_homology
  {V : Type u}
  [Category.{v} V]
  [Preadditive V]
  {c : ComplexShape ι}
  {C D : HomologicalComplex V c}
  {f₀ f₁ : C ⟶ D}
  {C : Type u₁}
  [Category.{v₁} C]
  [Preadditive C]
  [Limits.HasCoproducts.{w₁} C]
  [CategoryWithHomology C]
  {X Y : TopCat.{w₁}}
  {f g : X ⟶ Y}
  {H : TopCat.Homotopy f g}
  {R : C}
  {n : ℕ} :
-- imply
  ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map f = ((AlgebraicTopology.singularHomologyFunctor C n).obj R).map g := by
-- proof
  simp only [AlgebraicTopology.singularHomologyFunctor, Functor.comp_obj,
    Functor.whiskeringRight_obj_obj, Functor.comp_map]
  rw [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyFunctor_map]
  exact H.congr_homologyMap_singularChainComplexFunctor R n
end HomotopyInvariance
namespace HomotopyTheory
open CategoryTheory AlgebraicTopology HomologicalComplex Limits


namespace HomotopyTheory

/--
[isZero_singularHomology_of_contractibleSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean)
-/
@[path]
lemma isZero_singularHomology_of_contractibleSpace
  [Category C]
  [HasCoproducts.{0} C]
  [Preadditive C]
  [CategoryWithHomology C]
  {R : C}
  {n : ℕ}
  {X : TopCat.{0}}
  [ContractibleSpace X]
-- given
  (hn : n ≠ 0) :
-- imply
  IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
-- proof
  obtain ⟨b, ⟨H⟩⟩ := id_nullhomotopic X
  rw [IsZero.iff_id_eq_zero]
  rw [← CategoryTheory.Functor.map_id ((singularHomologyFunctor C n).obj R) X]
  have htpy : TopCat.Homotopy (𝟙 X) (topConstAt b) := H
  show homologyMap (((singularChainComplexFunctor C).obj R).map (𝟙 X)) n = 0
  rw [htpy.congr_homologyMap_singularChainComplexFunctor R n]
  rw [show topConstAt b = topProjToPoint X ≫ topInclFromPoint b from by ext; rfl]
  rw [CategoryTheory.Functor.map_comp, homologyMap_comp]
  have hZ : IsZero (((singularHomologyFunctor C n).obj R).obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R (TopCat.of PUnit) hn
  have h1 : homologyMap (((singularChainComplexFunctor C).obj R).map (topInclFromPoint b)) n = 0 :=
    hZ.eq_zero_of_src _
  simp only [h1, Limits.comp_zero]

end HomotopyTheory

namespace HomotopyInvariance

/--
[nonempty_singularChainHomotopy_of_homotopy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean)
-/
@[path]
lemma nonempty_singularChainHomotopy_of_homotopy
  {C : Type u'}
  [Category.{v'} C]
  [Preadditive C]
  [HasCoproducts.{w'} C]
  {X Y : TopCat.{w'}}
  {f₀ f₁ : X ⟶ Y}
  {H : TopCat.Homotopy f₀ f₁}
  {R : C} :
-- imply
  Nonempty (Homotopy (((singularChainComplexFunctor C).obj R).map f₀) (((singularChainComplexFunctor C).obj R).map f₁)) :=
-- proof
  ⟨singularChainHomotopy_of_homotopy H R⟩

end HomotopyInvariance

/--
[chainHomotopy_homologyMap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section5.lean)
-/
@[path]
private lemma chainHomotopy_homologyMap_eq_eq
  {V : Type u}
  [Category.{v} V]
  [Preadditive V]
  {c : ComplexShape ι}
  {C D : HomologicalComplex V c}
  {f₀ f₁ : C ⟶ D}
  {i : ι}
  [C.HasHomology i]
  [D.HasHomology i]
-- given
  (h : ChainHomotopy f₀ f₁) :
-- imply
  homologyMap f₀ i = homologyMap f₁ i := by
-- proof
  apply HomotopyInvariance.chainHomotopy_homologyMap_eq h i


-- created on 2026-10-23
