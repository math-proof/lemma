/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part27


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem cubicEquivalent_refl {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    cubicEquivalent c c := by
  refine ⟨rfl, rfl, ⟨0, Equiv.refl (Fin d), fun _ : Fin d => false, ?_⟩⟩
  simp


theorem cubicEquivalent_support_card {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    c'.support.card = c.support.card := by
  rcases h with ⟨_, _, v, σ, ε, hsupport⟩
  calc
    c'.support.card = c'.toPolymerSupport.carrier.card :=
      (toPolymerSupport_card c').symm
    _ = (c.toPolymerSupport.cubicTransform v σ ε).carrier.card := by
      rw [hsupport]
    _ = c.toPolymerSupport.carrier.card := by
      rw [PolymerSupport.cubicTransform_card]
    _ = c.support.card := toPolymerSupport_card c


theorem cubicEquivalent_coordinateDiameterBound {d R maxDegree maxRange D : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c')
    (hdiam : c.toPolymerSupport.coordinateDiameterBound D) :
    c'.toPolymerSupport.coordinateDiameterBound D := by
  rcases h with ⟨_, _, v, σ, ε, hsupport⟩
  rw [hsupport]
  exact PolymerSupport.coordinateDiameterBound_cubicTransform σ ε hdiam

theorem cubicEquivalent_symm {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    cubicEquivalent c' c := by
  rcases h with ⟨hdegree, hrange, v, σ, ε, hsupport⟩
  refine ⟨hdegree.symm, hrange.symm,
    ⟨PolymerSupport.cubicInverseTranslation v σ ε, σ.symm, fun i => ε (σ i), ?_⟩⟩
  have hback :
      c'.toPolymerSupport.cubicTransform
        (PolymerSupport.cubicInverseTranslation v σ ε) σ.symm
        (fun i => ε (σ i)) = c.toPolymerSupport := by
    rw [hsupport]
    simp [PolymerSupport.cubicInverseTranslation]
  exact hback.symm

theorem cubicEquivalent_trans {d R maxDegree maxRange : ℕ}
    {c₁ c₂ c₃ : BoundedPolymerCase d R maxDegree maxRange}
    (h₁₂ : cubicEquivalent c₁ c₂)
    (h₂₃ : cubicEquivalent c₂ c₃) :
    cubicEquivalent c₁ c₃ := by
  rcases h₁₂ with ⟨hdegree₁₂, hrange₁₂, v, σ, ε, hsupport₁₂⟩
  rcases h₂₃ with ⟨hdegree₂₃, hrange₂₃, w, τ, δ, hsupport₂₃⟩
  refine ⟨hdegree₁₂.trans hdegree₂₃, hrange₁₂.trans hrange₂₃,
    ⟨PolymerSupport.reflectCoordinatesSite δ
        (PolymerSupport.permuteCoordinatesSite τ v) + w,
      σ.trans τ, fun i => Bool.xor (ε (τ.symm i)) (δ i), ?_⟩⟩
  calc
    c₃.toPolymerSupport =
        c₂.toPolymerSupport.cubicTransform w τ δ := hsupport₂₃
    _ = (c₁.toPolymerSupport.cubicTransform v σ ε).cubicTransform w τ δ := by
      rw [hsupport₁₂]
    _ = c₁.toPolymerSupport.cubicTransform
        (PolymerSupport.reflectCoordinatesSite δ
          (PolymerSupport.permuteCoordinatesSite τ v) + w)
        (σ.trans τ) (fun i => Bool.xor (ε (τ.symm i)) (δ i)) := by
      rw [PolymerSupport.cubicTransform_cubicTransform]


theorem ofLocalCoordinate_cubicTransformLocalCoordinate_cubicEquivalent
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hbox' :
      (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicEquivalent
      (ofLocalCoordinate c hbox hdegree hrange)
      (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε)
        hbox' (by simpa using hdegree) (by simpa using hrange)) := by
  refine ⟨?_, ?_, v, σ, ε, ?_⟩
  · apply Fin.ext
    simp [ofLocalCoordinate, cubicTransformLocalCoordinate]
  · apply Fin.ext
    simp [ofLocalCoordinate, cubicTransformLocalCoordinate]
  · rw [toPolymerSupport_ofLocalCoordinate,
      toPolymerSupport_ofLocalCoordinate]
    rfl


theorem ofLocalCoordinate_permuteLocalCoordinate_cubicEquivalent
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (σ : Equiv.Perm (Fin d))
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicEquivalent
      (ofLocalCoordinate c hbox hdegree hrange)
      (ofLocalCoordinate (permuteLocalCoordinate c σ)
        (permuteLocalCoordinate_containedInBox c σ hbox)
        (by simpa using hdegree) (by simpa using hrange)) := by
  refine ⟨?_, ?_, 0, σ, (fun _ : Fin d => false), ?_⟩
  · apply Fin.ext
    simp [ofLocalCoordinate, permuteLocalCoordinate]
  · apply Fin.ext
    simp [ofLocalCoordinate, permuteLocalCoordinate]
  · rw [toPolymerSupport_ofLocalCoordinate,
      toPolymerSupport_ofLocalCoordinate]
    ext x
    change x ∈ c.support.permuteCoordinates σ ↔
      x ∈ c.support.cubicTransform (0 : Site d) σ
        (fun _ : Fin d => false)
    constructor
    · intro hx
      rcases (PolymerSupport.mem_permuteCoordinates c.support σ x).mp hx with
        ⟨y, hy, hxy⟩
      exact (PolymerSupport.mem_cubicTransform c.support
        (0 : Site d) σ (fun _ : Fin d => false) x).mpr
        ⟨y, hy, by simpa [PolymerSupport.cubicTransformSite] using hxy⟩
    · intro hx
      rcases (PolymerSupport.mem_cubicTransform c.support
          (0 : Site d) σ (fun _ : Fin d => false) x).mp hx with
        ⟨y, hy, hxy⟩
      exact (PolymerSupport.mem_permuteCoordinates c.support σ x).mpr
        ⟨y, hy, by simpa [PolymerSupport.cubicTransformSite] using hxy⟩


theorem ofLocalCoordinate_reflectLocalCoordinate_cubicEquivalent
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d)
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    cubicEquivalent
      (ofLocalCoordinate c hbox hdegree hrange)
      (ofLocalCoordinate (reflectLocalCoordinate c ε)
        (reflectLocalCoordinate_containedInBox c ε hbox)
        (by simpa using hdegree) (by simpa using hrange)) := by
  refine ⟨?_, ?_, 0, Equiv.refl (Fin d), ε, ?_⟩
  · apply Fin.ext
    simp [ofLocalCoordinate, reflectLocalCoordinate]
  · apply Fin.ext
    simp [ofLocalCoordinate, reflectLocalCoordinate]
  · rw [toPolymerSupport_ofLocalCoordinate,
      toPolymerSupport_ofLocalCoordinate]
    ext x
    change x ∈ c.support.reflectCoordinates ε ↔
      x ∈ c.support.cubicTransform (0 : Site d) (Equiv.refl (Fin d)) ε
    constructor
    · intro hx
      rcases (PolymerSupport.mem_reflectCoordinates c.support ε x).mp hx with
        ⟨y, hy, hxy⟩
      exact (PolymerSupport.mem_cubicTransform c.support
        (0 : Site d) (Equiv.refl (Fin d)) ε x).mpr
        ⟨y, hy, by simpa [PolymerSupport.cubicTransformSite] using hxy⟩
    · intro hx
      rcases (PolymerSupport.mem_cubicTransform c.support
          (0 : Site d) (Equiv.refl (Fin d)) ε x).mp hx with
        ⟨y, hy, hxy⟩
      exact (PolymerSupport.mem_reflectCoordinates c.support ε x).mpr
        ⟨y, hy, by simpa [PolymerSupport.cubicTransformSite] using hxy⟩


end BoundedPolymerCase
end
end Exact3D
end StatMech
