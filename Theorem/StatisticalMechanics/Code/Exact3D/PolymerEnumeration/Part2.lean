/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Instance.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part2


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace PolymerSupport

theorem finiteTranslationEquivalent_iff {d : ℕ} (P Q : PolymerSupport d) :
    finiteTranslationEquivalent P Q ↔ ∃ v : Site d, Q = P.translate v := by
  classical
  constructor
  · intro h
    rcases h with ⟨hP, hQ⟩ | ⟨v, htrans⟩
    · refine ⟨0, ?_⟩
      ext x
      simp [translate, hP, hQ]
    · exact ⟨v.1, htrans⟩
  · rintro ⟨v, htrans⟩
    by_cases hP : P.carrier = ∅
    · left
      refine ⟨hP, ?_⟩
      ext x
      simp [htrans, translate, hP]
    · right
      have hnonempty : P.carrier.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hP
      rcases hnonempty with ⟨x, hx⟩
      have hy : x + v ∈ Q := by
        rw [htrans]
        exact (mem_translate P v (x + v)).mpr ⟨x, hx, rfl⟩
      have hv : x + v - x = v := by
        ext i
        simp
      refine ⟨⟨v, ?_⟩, htrans⟩
      exact (mem_translationCandidateSet P Q v).mpr
        ⟨x + v, hy, x, hx, hv⟩


theorem cubicTransform_zero_translate {d : ℕ} (P : PolymerSupport d)
    (v : Site d) (σ : Equiv.Perm (Fin d)) (ε : CoordinateReflection d) :
    (P.cubicTransform (0 : Site d) σ ε).translate v =
      P.cubicTransform v σ ε := by
  ext x
  constructor
  · intro hx
    rcases (mem_translate (P.cubicTransform (0 : Site d) σ ε) v x).mp hx with
      ⟨y, hy, rfl⟩
    rcases (mem_cubicTransform P (0 : Site d) σ ε y).mp hy with
      ⟨z, hz, rfl⟩
    exact (mem_cubicTransform P v σ ε
      (cubicTransformSite (0 : Site d) σ ε z + v)).mpr
        ⟨z, hz, by simp [cubicTransformSite]⟩
  · intro hx
    rcases (mem_cubicTransform P v σ ε x).mp hx with ⟨z, hz, rfl⟩
    exact (mem_translate (P.cubicTransform (0 : Site d) σ ε) v
      (cubicTransformSite v σ ε z)).mpr
      ⟨cubicTransformSite (0 : Site d) σ ε z,
        (mem_cubicTransform P (0 : Site d) σ ε
          (cubicTransformSite (0 : Site d) σ ε z)).mpr ⟨z, hz, rfl⟩,
        by simp [cubicTransformSite]⟩

end PolymerSupport
end
end Exact3D
end StatMech
