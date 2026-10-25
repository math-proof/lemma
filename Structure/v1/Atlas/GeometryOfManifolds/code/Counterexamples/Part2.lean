/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Def.v1.Atlas.GeometryOfManifolds.code.Counterexamples.Part5
set_option autoImplicit false

open DifferentialFormSpace


/-- Data of the Kodaira–Thurston manifold: a compact symplectic $4$-manifold with $b_1 = 3$ (odd), hence not Kähler. -/
structure KodairaThurstonManifold where
  Ω : ℕ → Type*
  VF : Type*
  inst : DifferentialFormSpace Ω VF
  compact : @IsCompactSymplectic Ω VF inst
  bracket : @HasLieBracket Ω VF inst
  symplectic : @SymplecticManifold Ω VF inst
  J : @AlmostComplexStr Ω VF inst
  hodge : @HasHodgeNumbers Ω VF inst
  betti_one_eq_three : hodge.betti 1 = 3


/-- Data witnessing the connected sum $\mathbb{CP}^2 \# \mathbb{CP}^2 \# \mathbb{CP}^2$: a smooth $4$-manifold which is neither symplectic nor complex (no integrable almost complex structure). -/
structure CP2TripleSumData where
  Ω : ℕ → Type*
  VF : Type*
  inst : DifferentialFormSpace Ω VF
  J : @AlmostComplexStr Ω VF inst
  not_symplectic : ¬ Nonempty (@SymplecticManifold Ω VF inst)
  not_complex : ∀ (J' : @AlmostComplexStr Ω VF inst)
       (nij : @NijenhuisTensor Ω VF inst J'),
       ¬ @IsIntegrable Ω VF inst J' nij

