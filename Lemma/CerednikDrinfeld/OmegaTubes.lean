import Lemma.CerednikDrinfeld.DrinfeldHolomorphic
import Def.CerednikDrinfeld_OmegaTubes

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace CerednikDrinfeld.Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)


omit [DecidableEq K] in
theorem mem_stdEdgeTube_iff (z : K) : z ∈ stdEdgeTube ϖ ↔
    z ∈ upperHalfPlane K₀ K ∧ Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v z ∧ Valued.v z < 1 := Iff.rfl

omit [DecidableEq K] in
theorem stdEdgeTube_subset_upperHalfPlane : stdEdgeTube ϖ ⊆ upperHalfPlane K₀ K := fun _ h => h.1


theorem mem_vertexTube_iff (g : PGL(2, K₀)) (z : K) :
    z ∈ vertexTube ϖ g ↔ z ∈ upperHalfPlane K₀ K ∧ pmoebius K₀ g⁻¹ z ∈ affinoid ϖ 0 := Iff.rfl

theorem mem_edgeTube_iff (g : PGL(2, K₀)) (z : K) :
    z ∈ edgeTube ϖ g ↔ z ∈ upperHalfPlane K₀ K ∧ pmoebius K₀ g⁻¹ z ∈ stdEdgeTube ϖ := Iff.rfl

theorem vertexTube_subset_upperHalfPlane (g : PGL(2, K₀)) : vertexTube ϖ g ⊆ upperHalfPlane K₀ K := fun _ h => h.1

theorem edgeTube_subset_upperHalfPlane (g : PGL(2, K₀)) : edgeTube ϖ g ⊆ upperHalfPlane K₀ K := fun _ h => h.1

theorem vertexTube_one : vertexTube ϖ (1 : PGL(2, K₀)) = affinoid ϖ 0 := by
  ext z
  simp only [mem_vertexTube_iff, inv_one, pmoebius_one]
  exact ⟨fun h => h.2, fun h => ⟨affinoid_subset_upperHalfPlane ϖ 0 h, h⟩⟩

theorem edgeTube_one : edgeTube ϖ (1 : PGL(2, K₀)) = stdEdgeTube ϖ := by
  ext z
  simp only [mem_edgeTube_iff, inv_one, pmoebius_one]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

namespace IsometricAut

omit [DecidableEq K] in

theorem mapsTo_stdEdgeTube (s : IsometricAut K₀ K) : Set.MapsTo s.toRingEquiv (stdEdgeTube ϖ) (stdEdgeTube ϖ) := by
  rintro z ⟨hz, h1, h2⟩
  refine ⟨s.mapsTo_upperHalfPlane hz, ?_, ?_⟩
  · rw [s.isometry]; exact h1
  · rw [s.isometry]; exact h2

theorem mapsTo_vertexTube (s : IsometricAut K₀ K) (g : PGL(2, K₀)) :
    Set.MapsTo s.toRingEquiv (vertexTube ϖ g) (vertexTube ϖ g) := by
  rintro z ⟨hz, hg⟩
  refine ⟨s.mapsTo_upperHalfPlane hz, ?_⟩
  rw [← s.comm_pmoebius g⁻¹ hz]
  exact s.mapsTo_affinoid ϖ 0 hg

theorem mapsTo_edgeTube (s : IsometricAut K₀ K) (g : PGL(2, K₀)) :
    Set.MapsTo s.toRingEquiv (edgeTube ϖ g) (edgeTube ϖ g) := by
  rintro z ⟨hz, hg⟩
  refine ⟨s.mapsTo_upperHalfPlane hz, ?_⟩
  rw [← s.comm_pmoebius g⁻¹ hz]
  exact s.mapsTo_stdEdgeTube ϖ hg

theorem mem_vertexTube_iff_mem (s : IsometricAut K₀ K) (g : PGL(2, K₀)) (z : K) :
    s.toRingEquiv z ∈ vertexTube ϖ g ↔ z ∈ vertexTube ϖ g := by
  refine ⟨fun h => ?_, fun h => s.mapsTo_vertexTube ϖ g h⟩
  have := (s⁻¹).mapsTo_vertexTube ϖ g h
  simpa [inv_toRingEquiv] using this

theorem mem_edgeTube_iff_mem (s : IsometricAut K₀ K) (g : PGL(2, K₀)) (z : K) :
    s.toRingEquiv z ∈ edgeTube ϖ g ↔ z ∈ edgeTube ϖ g := by
  refine ⟨fun h => ?_, fun h => s.mapsTo_edgeTube ϖ g h⟩
  have := (s⁻¹).mapsTo_edgeTube ϖ g h
  simpa [inv_toRingEquiv] using this

end IsometricAut

end CerednikDrinfeld.Omega

end
