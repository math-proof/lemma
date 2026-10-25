/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Lemma.Fin.Any_Eq.of.Ne_0
import Lemma.Complex.Any_Any_And_All_Eq_AdjointAction.All_Finite.of.IsHarishChandraBimodule.IsIrreducible
import Def.v1.Atlas.LieGroups.code.HighestWeightModules.Part2
import Theorem.v1.Atlas.LieGroups.code.HarishChandraCorollaries
import Def.v1.Atlas.LieGroups.code.DufloJoseph


noncomputable section

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

@[elab_as_elim]
theorem UniversalEnvelopingAlgebra.induction
    {motive : UniversalEnvelopingAlgebra R 𝔤 → Prop}
    (halg : ∀ r, motive (algebraMap R (UniversalEnvelopingAlgebra R 𝔤) r))
    (hι : ∀ x, motive (UniversalEnvelopingAlgebra.ι R x))
    (hmul : ∀ a b, motive a → motive b → motive (a * b))
    (hadd : ∀ a b, motive a → motive b → motive (a + b))
    (u : UniversalEnvelopingAlgebra R 𝔤) : motive u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R (UniversalEnvelopingAlgebra.Rel R 𝔤) u
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact halg r
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

theorem uea_ad_leibniz (x : 𝔤) (a b : UniversalEnvelopingAlgebra R 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * (a * b) - (a * b) * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R x * a - a * UniversalEnvelopingAlgebra.ι R x) * b +
    a * (UniversalEnvelopingAlgebra.ι R x * b - b * UniversalEnvelopingAlgebra.ι R x) := by
  simp only [mul_sub, sub_mul, mul_assoc]; abel

theorem uea_ad_add (x : 𝔤) (v₁ v₂ : UniversalEnvelopingAlgebra R 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * (v₁ + v₂) - (v₁ + v₂) * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R x * v₁ - v₁ * UniversalEnvelopingAlgebra.ι R x) +
    (UniversalEnvelopingAlgebra.ι R x * v₂ - v₂ * UniversalEnvelopingAlgebra.ι R x) := by
  simp only [mul_add, add_mul]; abel

theorem uea_comm_rel (x y : 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
    UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R) ⁅x, y⁆ := by
  have h := (UniversalEnvelopingAlgebra.ι R (L := 𝔤)).map_lie (x := x) (y := y)
  simp only [LieRing.of_associative_ring_bracket] at h
  exact h.symm

end
