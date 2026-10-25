/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Submodule.Any_EqAndAll_Eq_V.of.IsSubspaceIsometry.EqOrthogonalBilinFormTop_Bot.All_Eq
import Def.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part4


namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- **B-N pair data** for the oriflamme building: Borel and frame-stabiliser subsets of the
isometry group, an oriflamme chamber, a frame, and the Bruhat decomposition
$G = B \cdot W \cdot B$. -/
structure BNPairData where
  borelSet : Set (V ≃ₗ[k] V)
  frameStabSet : Set (V ≃ₗ[k] V)
  borel_sub : borelSet ⊆ OriflammeIsometryGroup k V B
  frameStab_sub : frameStabSet ⊆ OriflammeIsometryGroup k V B
  chamber : OriflammeChamber k V B n
  borel_stab_chain : ∀ g ∈ borelSet, ∀ i,
    (chamber.chain i).map g.toLinearMap = chamber.chain i
  borel_stab_top₁ : ∀ g ∈ borelSet,
    chamber.top₁.map g.toLinearMap = chamber.top₁
  borel_stab_top₂ : ∀ g ∈ borelSet,
    chamber.top₂.map g.toLinearMap = chamber.top₂
  frame : OriflammeFrame k V B n
  frameStab_permutes : ∀ g ∈ frameStabSet, ∀ ib : Fin n × Bool,
    ∃ jb : Fin n × Bool, (frame.lines ib).map g.toLinearMap = frame.lines jb
  bruhat : ∀ g ∈ OriflammeIsometryGroup k V B,
    ∃ w ∈ frameStabSet, ∃ b₁ ∈ borelSet, ∃ b₂ ∈ borelSet,
      g = b₁.trans (w.trans b₂)


end Oriflamme
