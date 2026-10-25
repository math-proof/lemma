/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section22.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Module.Projective
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.FundamentalThm
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section22


namespace FundamentalHomologicalAlgebra

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Uniqueness up to chain homotopy** in Theorem 22.1: any two chain maps
`g, h : P.complex → Q.complex` between a projective resolution `P` of `Y`
and a resolution `Q` of `Z`, both covering the same map `f : Y → Z`, are
chain homotopic.  Combined with `lift` this produces a well-defined map on
derived functors. -/
noncomputable def liftUniqueUpToHomotopy {Y Z : C} (f : Y ⟶ Z)
    {P : ProjectiveResolution Y} {Q : FundamentalThm.Resolution Z}
    (g h : P.complex ⟶ Q.complex)
    (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    Homotopy g h :=
  FundamentalThm.liftHomotopy f g h g_comm h_comm

/-- **Theorem 22.1 (Fundamental Theorem of Homological Algebra).**  Given a
map `f : Y → Z` in an abelian category, a projective resolution `P` of `Y`,
and any resolution `Q` of `Z`, there exists a chain map
`g : P.complex → Q.complex` covering `f` (i.e. with
`g ≫ Q.π = P.π ≫ (single₀).map f`); moreover any other chain map covering
`f` is chain homotopic to `g`.  This packaged form returns the lift,
together with the commutativity equation and the uniqueness statement, all
in a single bundled term. -/
noncomputable def fundamentalTheorem {Y Z : C}
    (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : FundamentalThm.Resolution Z) :
    { g : P.complex ⟶ Q.complex //
      g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f ∧
      ∀ h : P.complex ⟶ Q.complex,
        h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f → Nonempty (Homotopy g h) } :=
  ⟨lift f P Q, lift_commutes f P Q, fun h hcomm =>
    ⟨liftUniqueUpToHomotopy f (lift f P Q) h (lift_commutes f P Q) hcomm⟩⟩

end FundamentalHomologicalAlgebra
