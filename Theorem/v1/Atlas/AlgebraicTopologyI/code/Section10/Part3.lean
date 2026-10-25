/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part5
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- For a fixed abelian group `R`, the constant-coefficient `J ↦ ⊕_J R` functor sends
injective functions to monomorphisms. (Split mono when `J` is nonempty; zero object when
empty.) -/
lemma sigmaConst_map_mono_of_injective
    (J K : Type) (f : J → K) (hf : Function.Injective f)
    (R : AddCommGrpCat) :
    Mono ((sigmaConst.obj R).map (show J ⟶ K from f)) := by
  by_cases hJ : Nonempty J
  · exact (⟨Function.invFun f, Function.invFun_comp hf⟩ :
      SplitMono (show J ⟶ K from f)).map (sigmaConst.obj R) |>.mono
  · rw [not_nonempty_iff] at hJ
    exact (show IsZero ((sigmaConst.obj R).obj J) by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro j; exact (hJ.false j).elim).mono _

end
end Excision
