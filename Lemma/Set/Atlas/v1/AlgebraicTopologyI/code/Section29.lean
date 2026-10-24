import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section29
open DirectSum GradedMonoid CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI SingularCohomology CupProduct
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI
open CategoryTheory AlgebraicTopology Limits
open CategoryTheory AlgebraicTopology AlgebraicTopologyI


namespace SingularCohomology

/--
[cupProduct_mul_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cupProduct_mul_zero
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {i j : ℕ}
  {a : singularCohomologyFamily R X i} :
-- imply
  GradedMonoid.GMul.mul a (0 : singularCohomologyFamily R X j) = 0 := by
-- proof
  show cupMul R X a 0 = 0
  simp only [cupMul, TensorProduct.tmul_zero, map_zero]

end SingularCohomology

namespace SingularCohomology

/--
[cupProduct_zero_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cupProduct_zero_mul
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {i j : ℕ}
  {b : singularCohomologyFamily R X j} :
-- imply
  GradedMonoid.GMul.mul (0 : singularCohomologyFamily R X i) b = 0 := by
-- proof
  show cupMul R X 0 b = 0
  simp only [cupMul, TensorProduct.zero_tmul, map_zero]

end SingularCohomology

namespace SingularCohomology

/--
[cupProduct_mul_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cupProduct_mul_add
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {i j : ℕ}
  {a : singularCohomologyFamily R X i}
  {b c : singularCohomologyFamily R X j} :
-- imply
  GradedMonoid.GMul.mul a (b + c) = GradedMonoid.GMul.mul a b + GradedMonoid.GMul.mul a c := by
-- proof
  show cupMul R X a (b + c) = cupMul R X a b + cupMul R X a c
  simp only [cupMul, TensorProduct.tmul_add, map_add]

end SingularCohomology

namespace SingularCohomology

/--
[cupProduct_add_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cupProduct_add_mul
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {i j : ℕ}
  {a b : singularCohomologyFamily R X i}
  {c : singularCohomologyFamily R X j} :
-- imply
  GradedMonoid.GMul.mul (a + b) c = GradedMonoid.GMul.mul a c + GradedMonoid.GMul.mul b c := by
-- proof
  show cupMul R X (a + b) c = cupMul R X a c + cupMul R X b c
  simp only [cupMul, TensorProduct.add_tmul, map_add]

end SingularCohomology

namespace SingularCohomology

/--
[cupProduct_natCast_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cupProduct_natCast_zero
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}} :
-- imply
  cupProduct_natCast R X 0 = 0 :=
-- proof
  rfl

end SingularCohomology

namespace SingularCohomology

/--
[cupProduct_natCast_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cupProduct_natCast_succ
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {n : ℕ} :
-- imply
  cupProduct_natCast R X (n + 1) = cupProduct_natCast R X n + GradedMonoid.GOne.one :=
-- proof
  rfl

end SingularCohomology

namespace SingularCohomology

/--
[cupProduct_intCast_ofNat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cupProduct_intCast_ofNat
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {n : ℕ} :
-- imply
  cupProduct_intCast R X ↑n = cupProduct_natCast R X n :=
-- proof
  rfl

end SingularCohomology

namespace SingularCohomology

/--
[cupProduct_intCast_negSucc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cupProduct_intCast_negSucc
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {n : ℕ} :
-- imply
  cupProduct_intCast R X (Int.negSucc n) = -cupProduct_natCast R X (n + 1) :=
-- proof
  rfl

end SingularCohomology

namespace SingularCohomology

/--
[cohomologyAlgebraMap_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cohomologyAlgebraMap_one
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}} :
-- imply
  cohomologyAlgebraMap R X 1 = GradedMonoid.GOne.one := by
-- proof
  show (1 : R) • cohomologyUnit R X = cohomologyUnit R X
  simp [one_smul]

end SingularCohomology

namespace SingularCohomology

/--
[cast_smul_family](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma cast_smul_family
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {n m : ℕ}
  {r : R}
  {z : singularCohomologyFamily R X n}
-- given
  (h : n = m) :
-- imply
  cast (congrArg (singularCohomologyFamily R X) h) (r • z) = r • cast (congrArg (singularCohomologyFamily R X) h) z := by
-- proof
  subst h; rfl

end SingularCohomology

namespace CupProduct

/--
[sphereChainZ_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma sphereChainZ_free
  {R : Type}
  [CommRing R]
  {m : ℕ}
  {i : ℕ} :
-- imply
  Module.Free ℤ ((sphereChainZ m).X i) := by
-- proof
  show Module.Free ℤ
    ↑(∐ fun (_ : (TopCat.toSSet.obj (TopCat.sphere m)).obj
      (Opposite.op (SimplexCategory.mk i))) => ModuleCat.of ℤ ℤ)
  classical
  exact Module.Free.of_equiv'
    (Module.Free.directSum ℤ (fun _ => ↑(ModuleCat.of ℤ ℤ)))
    (ModuleCat.coprodIsoDirectSum _).toLinearEquiv.symm

end CupProduct

namespace CupProduct

/--
[moduleCat_singularHomology_isZero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma moduleCat_singularHomology_isZero_iff
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}}
  {n : ℕ} :
-- imply
  IsZero ((((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).homology n) ↔ IsZero ((((singularChainComplexFunctor.{0} AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj X).homology n) := by
-- proof
  set F := forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat
  set K_mod := (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X)
  set K_ab := (((singularChainComplexFunctor.{0} AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).obj X)
  have bridge : F.obj (K_mod.homology n) ≅ K_ab.homology n :=
    ((K_mod.sc n).mapHomologyIso F).symm ≪≫
    HomologicalComplex.homologyMapIso (iso := singularChainComplexFunctor_forget₂_iso X) (i := n)
  constructor
  · intro h
    exact IsZero.of_iso (Functor.map_isZero F h) bridge.symm
  · intro h
    exact IsZero.of_full_of_faithful_of_isZero F _ (IsZero.of_iso h bridge)

end CupProduct

namespace CupProduct

/--
[sphereChainZ_homology_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma sphereChainZ_homology_isZero
  {R : Type}
  [CommRing R]
  {m n : ℕ}
-- given
  (hn_lt : n < m)
  (hn_pos : 0 < n) :
-- imply
  IsZero ((sphereChainZ m).homology n) := by
-- proof
  have e_chain : sphereChainZ m ≅
    (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (SphereHomology.Sphere m))) :=
    ((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
      (sphereTopCatIso m)
  exact IsZero.of_iso
    ((moduleCat_singularHomology_isZero_iff (TopCat.of (SphereHomology.Sphere m)) n).mpr
      (SphereHomology.sphere_homology_vanishing n m (by omega) (by omega) (by omega)))
    (HomologicalComplex.homologyMapIso (iso := e_chain) (i := n))

end CupProduct

namespace CupProduct

/--
[isZero_Ext_of_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma isZero_Ext_of_isZero
  {R : Type}
  [CommRing R]
  {X : ModuleCat.{0} ℤ}
  {Y : ModuleCat.{0} ℤ}
  {n : ℕ}
-- given
  (hX : IsZero X) :
-- imply
  IsZero (((Ext ℤ (ModuleCat.{0} ℤ) n).obj (Opposite.op X)).obj Y) := by
-- proof
  haveI : CategoryTheory.Projective X := hX.projective
  cases n with
  | zero =>
    refine IsZero.of_iso ?_ ((CategoryTheory.ProjectiveResolution.self X).isoExt 0 Y)
    rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
    refine ShortComplex.exact_of_isZero_X₂ _ ?_
    dsimp [ChainComplex.linearYonedaObj]
    rw [IsZero.iff_id_eq_zero]
    ext (f : X ⟶ Y)
    exact (hX.eq_of_src f 0).symm ▸ rfl
  | succ k =>
    exact isZero_Ext_succ_of_projective X Y k

end CupProduct

namespace CupProduct

/--
[sphereChainZ_ext0_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
lemma sphereChainZ_ext0_isZero
  {R : Type}
  [CommRing R]
  {m n : ℕ}
-- given
  (hn_lt : n < m)
  (hn_pos : 0 < n) :
-- imply
  IsZero (((Ext ℤ (ModuleCat.{0} ℤ) 0).obj (Opposite.op ((sphereChainZ m).homology n))).obj (ModuleCat.of ℤ ℤ)) :=
-- proof
  isZero_Ext_of_isZero (sphereChainZ_homology_isZero m n hn_lt hn_pos) _ 0
/-- Vanishing of sphere cohomology in intermediate degrees:
$H^n(S^m; \mathbb{Z}) = 0$ for $0 < n < m$. Combines the UCT short exact sequence
with the vanishing of the relevant Ext terms. -/
end CupProduct
namespace SphereHomology
open CategoryTheory AlgebraicTopology AlgebraicTopologyI


/--
[augmentationCocycle_coboundary_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean)
-/
@[path]
private lemma augmentationCocycle_coboundary_zero_eq
  {R : Type}
  [CommRing R]
  {R : Type}
  [CommRing R]
  {X : TopCat.{0}} :
-- imply
  (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).d 1 0 ≫ augmentationCocycle R X = 0 := by
-- proof
  apply SingularCohomology.augmentationCocycle_coboundary_zero R R X


-- created on 2026-10-23
