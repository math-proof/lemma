/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CupProductHelpers
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section26
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct


noncomputable section

namespace SingularCohomology

/-- The diagonal $X \to X \times X$, $x \mapsto (x, x)$. -/
def TopCat.diag (X : TopCat.{0}) : X ⟶ TopCat.of (X × X) :=
  ⟨fun x => (x, x), by fun_prop⟩

/-- The map on $n$th homology induced by the diagonal $X \to X \times X$. -/
def diagHomology (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    singularHomologyFamily R X n →ₗ[R]
      singularHomologyFamily R (TopCat.of (X × X)) n :=
  (((singularHomologyFunctor (ModuleCat.{0} R) n).obj (ModuleCat.of R R)).map
    (TopCat.diag X)).hom

/-- The total map on graded homology $H_*(X) \to H_*(X \times X)$ induced by the diagonal,
half of the comultiplication on the graded coalgebra $H_*(X; R)$ of Corollary 26.2. -/
def totalDiagMap (R : Type) [CommRing R] (X : TopCat.{0}) :
    totalSingularHomology R X →ₗ[R]
      totalSingularHomology R (TopCat.of (X × X)) :=
  @DirectSum.lmap R _ ℕ (singularHomologyFamily R X) _ _
    (singularHomologyFamily R (TopCat.of (X × X))) _ _
    (fun n => diagHomology R X n)

end SingularCohomology

end

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory

open scoped TensorProduct

open SingularCohomology


/-- The homology cross product in a fixed bidegree:
$H_p(X) \otimes_R H_q(Y) \to H_{p+q}(X \times Y)$. -/
noncomputable def toTerminal (X : TopCat.{0}) : X ⟶ TopCat.of PUnit.{1} :=
  ⟨fun _ => PUnit.unit, continuous_const⟩

/-- The map $H_0(X; R) \to H_0(\{\ast\}; R)$ induced by collapsing $X$ to a point. -/
noncomputable def h0MapToTerminal
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularHomologyModule R X 0 ⟶ singularHomologyModule R (TopCat.of PUnit.{1}) 0 :=
  (((singularHomologyFunctor (ModuleCat.{0} R) 0).obj (ModuleCat.of R R)).map (toTerminal X))

/-- The zeroth homology of the singleton, identified with a coproduct of one copy of $R$. -/
noncomputable def h0TerminalIsoCoproduct (R : Type) [CommRing R] :
    singularHomologyModule R (TopCat.of PUnit.{1}) 0 ≅
      ∐ fun _ : (TopCat.of PUnit.{1} : Type) ↦ (ModuleCat.of R R) :=
  singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    (ModuleCat.{0} R) (ModuleCat.of R R) (TopCat.of PUnit)

/-- The fold map collapsing a one-element coproduct of $R$ to $R$. -/
noncomputable def coproductPUnitFold (R : Type) [CommRing R] :
    (∐ fun _ : (TopCat.of PUnit.{1} : Type) ↦ (ModuleCat.of R R)) ⟶ ModuleCat.of R R :=
  Limits.Sigma.desc (fun _ => 𝟙 _)

/-- The augmentation $H_0(X; R) \to R$, obtained by collapsing $X$ to a point. -/
noncomputable def augmentationH0
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularHomologyModule R X 0 ⟶ ModuleCat.of R R :=
  h0MapToTerminal R X ≫ (h0TerminalIsoCoproduct R).hom ≫ coproductPUnitFold R

/-- The counit $\varepsilon : H_*(X; R) \to R$ for the graded coalgebra structure of
Corollary 26.2: project to the degree-$0$ component and then augment. -/
noncomputable def augmentation
    (R : Type) [CommRing R]
    (X : TopCat.{0}) :
    totalSingularHomology R X →ₗ[R] R :=
  (augmentationH0 R X).hom ∘ₗ DirectSum.component R ℕ (singularHomologyFamily R X) 0

/-- Coassociativity of the comultiplication on $H_*(X; R)$: $(\Delta \otimes 1) \circ \Delta =
(1 \otimes \Delta) \circ \Delta$. -/

namespace SingularCohomology

/-- **Corollary 26.2**. If $R$ is a PID and $H_*(X; R)$ is free over $R$, then $H_*(X; R)$ is
a commutative graded coalgebra over $R$ (Definition 26.1): the comultiplication is induced by
the diagonal via Künneth, the augmentation is the counit, and the structure is graded
cocommutative. -/
def inducedCochainMap (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularCochainComplex R Y (ModuleCat.of R R) ⟶
    singularCochainComplex R X (ModuleCat.of R R) :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).map f)).op)

/-- The induced map on $n$th singular cohomology $f^* : H^n(Y; R) \to H^n(X; R)$. -/
def singularCohomologyMap (R : Type) [CommRing R]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singularCohomology R Y (ModuleCat.of R R) n ⟶
    singularCohomology R X (ModuleCat.of R R) n :=
  HomologicalComplex.homologyMap (inducedCochainMap R f) n

section AlexanderWhitney

/-- The Alexander–Whitney "front face" $\alpha_p : [p] \to [p+q]$ sending $i \mapsto i$. -/
def awFrontFace (p q : ℕ) : SimplexCategory.mk p ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom ⟨fun i => (Fin.castAdd q i).cast (by omega),
    fun _ _ h => by simp only [Fin.le_def]; exact h⟩

/-- The Alexander–Whitney "back face" $\omega_q : [q] \to [p+q]$ sending $j \mapsto j + p$. -/
def awBackFace (p q : ℕ) : SimplexCategory.mk q ⟶ SimplexCategory.mk (p + q) :=
  SimplexCategory.mkHom ⟨fun j => (Fin.natAdd p j).cast (by omega),
    fun _ _ h => by show (Fin.cast _ (Fin.natAdd p _)).val ≤ _
                    simp only [Fin.val_cast, Fin.val_natAdd]; omega⟩

/-- The Alexander–Whitney "front" $\sigma \mapsto \sigma \circ \alpha_p$ of a $(p+q)$-simplex. -/
def awFront (Z : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk (p + q)))) :
    (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk p)) :=
  (TopCat.toSSet.obj Z).map (awFrontFace p q).op σ

/-- The Alexander–Whitney "back" $\sigma \mapsto \sigma \circ \omega_q$ of a $(p+q)$-simplex. -/
def awBack (Z : TopCat.{0}) (p q : ℕ)
    (σ : (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk (p + q)))) :
    (TopCat.toSSet.obj Z).obj (Opposite.op (SimplexCategory.mk q)) :=
  (TopCat.toSSet.obj Z).map (awBackFace p q).op σ

/-- Evaluate a morphism from a coproduct of copies of $R$ at a fixed index $\sigma$. -/
def evalGen (R : Type) [CommRing R] {α : Type}
    (φ : (∐ fun (_ : α) => ModuleCat.of R R) ⟶ ModuleCat.of R R) (σ : α) : R :=
  (Sigma.ι (fun (_ : α) => ModuleCat.of R R) σ ≫ φ).hom (1 : R)

end AlexanderWhitney

/-- Evaluation of a singular $n$-cochain at a singular $n$-simplex $\sigma$, as an $R$-linear
map $S^n(Z; R) \to R$. -/
def evalAtSimplex (R : Type) [CommRing R] {n : ℕ} (Z : TopCat.{0}) (σ : (TopCat.toSSet.obj Z).obj
    (Opposite.op (SimplexCategory.mk n))) :
    (singularCochainComplex R Z (ModuleCat.of R R)).X n →ₗ[R] R where
  toFun φ := (Sigma.ι (fun (_ : (TopCat.toSSet.obj Z).obj
    (Opposite.op (SimplexCategory.mk n))) => ModuleCat.of R R) σ ≫ φ).hom (1 : R)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end SingularCohomology
