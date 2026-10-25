/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Def.MeasureTheory.Geometry.BanachTarski.Part12


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The free locus duplicates: each half is congruent to the whole. -/
theorem btOmega_halves :
    btCongr (btQ₁ ∪ btQ₂) btOmega ∧
    btCongr (btQ₃ ∪ btQ₄) btOmega ∧
    Disjoint (btQ₁ ∪ btQ₂) (btQ₃ ∪ btQ₄) ∧
    (btQ₁ ∪ btQ₂) ∪ (btQ₃ ∪ btQ₄) = btOmega := by
  have hQ1 : ∀ (x : btE) (hx : x ∈ btOmega),
      x ∈ btQ₁ ↔ btGamma ⟨x, hx⟩ ∈ btP₁ := by
    intro x hx
    simp only [btQ₁, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h', hh'⟩
      have heq : ((⟨x, h'⟩ : {x : btE // x ∈ btOmega}) = ⟨x, hx⟩) := rfl
      rw [heq] at hh'
      exact hh'
    · intro hh
      exact ⟨hx, hh⟩
  have hQ2 : ∀ (x : btE) (hx : x ∈ btOmega),
      x ∈ btQ₂ ↔ btGamma ⟨x, hx⟩ ∈ btP₂ := by
    intro x hx
    simp only [btQ₂, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h', hh'⟩
      have heq : ((⟨x, h'⟩ : {x : btE // x ∈ btOmega}) = ⟨x, hx⟩) := rfl
      rw [heq] at hh'
      exact hh'
    · intro hh
      exact ⟨hx, hh⟩
  have hQ3 : ∀ (x : btE) (hx : x ∈ btOmega),
      x ∈ btQ₃ ↔ btGamma ⟨x, hx⟩ ∈ btP₃ := by
    intro x hx
    simp only [btQ₃, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h', hh'⟩
      have heq : ((⟨x, h'⟩ : {x : btE // x ∈ btOmega}) = ⟨x, hx⟩) := rfl
      rw [heq] at hh'
      exact hh'
    · intro hh
      exact ⟨hx, hh⟩
  have hQ4 : ∀ (x : btE) (hx : x ∈ btOmega),
      x ∈ btQ₄ ↔ btGamma ⟨x, hx⟩ ∈ btP₄ := by
    intro x hx
    simp only [btQ₄, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h', hh'⟩
      have heq : ((⟨x, h'⟩ : {x : btE // x ∈ btOmega}) = ⟨x, hx⟩) := rfl
      rw [heq] at hh'
      exact hh'
    · intro hh
      exact ⟨hx, hh⟩
  have hsub1 : btQ₁ ⊆ btOmega := by
    intro x hx
    simp only [btQ₁, Set.mem_ofPred_eq] at hx
    exact hx.1
  have hsub2 : btQ₂ ⊆ btOmega := by
    intro x hx
    simp only [btQ₂, Set.mem_ofPred_eq] at hx
    exact hx.1
  have hsub3 : btQ₃ ⊆ btOmega := by
    intro x hx
    simp only [btQ₃, Set.mem_ofPred_eq] at hx
    exact hx.1
  have hsub4 : btQ₄ ⊆ btOmega := by
    intro x hx
    simp only [btQ₄, Set.mem_ofPred_eq] at hx
    exact hx.1
  obtain ⟨d12, d13, d14, d23, d24, d34, hunion⟩ := btFree_pieces
  have himg2 : btAct (FreeGroup.of (0 : Fin 2)) '' btQ₂ = btOmega \ btQ₁ := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hxQ2, rfl⟩
      simp only [btQ₂, Set.mem_ofPred_eq] at hxQ2
      obtain ⟨hxO, hxP⟩ := hxQ2
      have hyO : btAct (FreeGroup.of 0) x ∈ btOmega :=
        btOmega_invariant _ _ hxO
      have hgam : btGamma ⟨btAct (FreeGroup.of 0) x, hyO⟩ =
          FreeGroup.of 0 * btGamma ⟨x, hxO⟩ :=
        btGamma_act (FreeGroup.of 0) ⟨x, hxO⟩ hyO
      refine ⟨hyO, ?_⟩
      intro hyQ1
      have hP1 : btGamma ⟨btAct (FreeGroup.of 0) x, hyO⟩ ∈ btP₁ :=
        (hQ1 _ hyO).mp hyQ1
      rw [hgam] at hP1
      have hcompl : FreeGroup.of (0 : Fin 2) * btGamma ⟨x, hxO⟩ ∈ btP₁ᶜ := by
        rw [← btFree_image_P2]
        exact ⟨btGamma ⟨x, hxO⟩, hxP, rfl⟩
      exact hcompl hP1
    · rintro ⟨hyO, hyQ1⟩
      have hP1 : btGamma ⟨y, hyO⟩ ∉ btP₁ :=
        fun hP => hyQ1 ((hQ1 y hyO).mpr hP)
      have himg : btGamma ⟨y, hyO⟩ ∈
          (fun w => FreeGroup.of (0 : Fin 2) * w) '' btP₂ := by
        rw [btFree_image_P2]
        exact hP1
      obtain ⟨u, huP2, hu_eq⟩ := himg
      have hxO : btAct (FreeGroup.of (0 : Fin 2))⁻¹ y ∈ btOmega :=
        btOmega_invariant _ _ hyO
      have hgamx : btGamma ⟨btAct (FreeGroup.of (0 : Fin 2))⁻¹ y, hxO⟩ =
          (FreeGroup.of (0 : Fin 2))⁻¹ * btGamma ⟨y, hyO⟩ :=
        btGamma_act (FreeGroup.of (0 : Fin 2))⁻¹ ⟨y, hyO⟩ hxO
      have hu_eq2 : (FreeGroup.of (0 : Fin 2))⁻¹ * btGamma ⟨y, hyO⟩ = u := by
        rw [← hu_eq, inv_mul_cancel_left]
      have hxQ2 : btAct (FreeGroup.of (0 : Fin 2))⁻¹ y ∈ btQ₂ := by
        rw [hQ2 _ hxO, hgamx, hu_eq2]
        exact huP2
      refine ⟨btAct (FreeGroup.of (0 : Fin 2))⁻¹ y, hxQ2, ?_⟩
      rw [← btAct_mul, mul_inv_cancel, btAct_one]
  have himg4 : btAct (FreeGroup.of (1 : Fin 2)) '' btQ₄ = btOmega \ btQ₃ := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hxQ4, rfl⟩
      simp only [btQ₄, Set.mem_ofPred_eq] at hxQ4
      obtain ⟨hxO, hxP⟩ := hxQ4
      have hyO : btAct (FreeGroup.of 1) x ∈ btOmega :=
        btOmega_invariant _ _ hxO
      have hgam : btGamma ⟨btAct (FreeGroup.of 1) x, hyO⟩ =
          FreeGroup.of 1 * btGamma ⟨x, hxO⟩ :=
        btGamma_act (FreeGroup.of 1) ⟨x, hxO⟩ hyO
      refine ⟨hyO, ?_⟩
      intro hyQ3
      have hP3 : btGamma ⟨btAct (FreeGroup.of 1) x, hyO⟩ ∈ btP₃ :=
        (hQ3 _ hyO).mp hyQ3
      rw [hgam] at hP3
      have hcompl : FreeGroup.of (1 : Fin 2) * btGamma ⟨x, hxO⟩ ∈ btP₃ᶜ := by
        rw [← btFree_image_P4]
        exact ⟨btGamma ⟨x, hxO⟩, hxP, rfl⟩
      exact hcompl hP3
    · rintro ⟨hyO, hyQ3⟩
      have hP3 : btGamma ⟨y, hyO⟩ ∉ btP₃ :=
        fun hP => hyQ3 ((hQ3 y hyO).mpr hP)
      have himg : btGamma ⟨y, hyO⟩ ∈
          (fun w => FreeGroup.of (1 : Fin 2) * w) '' btP₄ := by
        rw [btFree_image_P4]
        exact hP3
      obtain ⟨u, huP4, hu_eq⟩ := himg
      have hxO : btAct (FreeGroup.of (1 : Fin 2))⁻¹ y ∈ btOmega :=
        btOmega_invariant _ _ hyO
      have hgamx : btGamma ⟨btAct (FreeGroup.of (1 : Fin 2))⁻¹ y, hxO⟩ =
          (FreeGroup.of (1 : Fin 2))⁻¹ * btGamma ⟨y, hyO⟩ :=
        btGamma_act (FreeGroup.of (1 : Fin 2))⁻¹ ⟨y, hyO⟩ hxO
      have hu_eq2 : (FreeGroup.of (1 : Fin 2))⁻¹ * btGamma ⟨y, hyO⟩ = u := by
        rw [← hu_eq, inv_mul_cancel_left]
      have hxQ4 : btAct (FreeGroup.of (1 : Fin 2))⁻¹ y ∈ btQ₄ := by
        rw [hQ4 _ hxO, hgamx, hu_eq2]
        exact huP4
      refine ⟨btAct (FreeGroup.of (1 : Fin 2))⁻¹ y, hxQ4, ?_⟩
      rw [← btAct_mul, mul_inv_cancel, btAct_one]
  have hunion1 : btQ₁ ∪ (btOmega \ btQ₁) = btOmega := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (hx | ⟨hxO, -⟩)
      · exact hsub1 hx
      · exact hxO
    · intro hxO
      by_cases hx : x ∈ btQ₁
      · exact Or.inl hx
      · exact Or.inr ⟨hxO, hx⟩
  have hunion3 : btQ₃ ∪ (btOmega \ btQ₃) = btOmega := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (hx | ⟨hxO, -⟩)
      · exact hsub3 hx
      · exact hxO
    · intro hxO
      by_cases hx : x ∈ btQ₃
      · exact Or.inl hx
      · exact Or.inr ⟨hxO, hx⟩
  have dA : Disjoint btQ₁ btQ₂ := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have hxO : x ∈ btOmega := hsub1 hx1
    exact Set.disjoint_left.mp d12 ((hQ1 x hxO).mp hx1) ((hQ2 x hxO).mp hx2)
  have dC : Disjoint btQ₃ btQ₄ := by
    rw [Set.disjoint_left]
    intro x hx3 hx4
    have hxO : x ∈ btOmega := hsub3 hx3
    exact Set.disjoint_left.mp d34 ((hQ3 x hxO).mp hx3) ((hQ4 x hxO).mp hx4)
  have hcongr12 : btCongr (btQ₁ ∪ btQ₂) btOmega := by
    have h1 := btCongr_refl btQ₁
    have h2 := btCongr_self_image (btAct (FreeGroup.of (0 : Fin 2))) btQ₂
    rw [himg2] at h2
    have dB : Disjoint btQ₁ (btOmega \ btQ₁) := by
      rw [Set.disjoint_left]
      intro x hx1 hxD
      obtain ⟨-, hnQ1⟩ := hxD
      exact hnQ1 hx1
    have hun := btCongr_union h1 h2 dA dB
    rw [hunion1] at hun
    exact hun
  have hcongr34 : btCongr (btQ₃ ∪ btQ₄) btOmega := by
    have h1 := btCongr_refl btQ₃
    have h2 := btCongr_self_image (btAct (FreeGroup.of (1 : Fin 2))) btQ₄
    rw [himg4] at h2
    have dB : Disjoint btQ₃ (btOmega \ btQ₃) := by
      rw [Set.disjoint_left]
      intro x hx3 hxD
      obtain ⟨-, hnQ3⟩ := hxD
      exact hnQ3 hx3
    have hun := btCongr_union h1 h2 dC dB
    rw [hunion3] at hun
    exact hun
  refine ⟨hcongr12, hcongr34, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx12 hx34
    simp only [Set.mem_union] at hx12 hx34
    have hxO : x ∈ btOmega := by
      rcases hx12 with hx1 | hx2
      · exact hsub1 hx1
      · exact hsub2 hx2
    rcases hx12 with hx1 | hx2 <;> rcases hx34 with hx3 | hx4
    · exact Set.disjoint_left.mp d13 ((hQ1 x hxO).mp hx1) ((hQ3 x hxO).mp hx3)
    · exact Set.disjoint_left.mp d14 ((hQ1 x hxO).mp hx1) ((hQ4 x hxO).mp hx4)
    · exact Set.disjoint_left.mp d23 ((hQ2 x hxO).mp hx2) ((hQ3 x hxO).mp hx3)
    · exact Set.disjoint_left.mp d24 ((hQ2 x hxO).mp hx2) ((hQ4 x hxO).mp hx4)
  · ext x
    simp only [Set.mem_union]
    constructor
    · rintro ((hx1 | hx2) | hx3 | hx4)
      · exact hsub1 hx1
      · exact hsub2 hx2
      · exact hsub3 hx3
      · exact hsub4 hx4
    · intro hxO
      have hmem : btGamma ⟨x, hxO⟩ ∈ btP₁ ∪ btP₂ ∪ btP₃ ∪ btP₄ := by
        rw [hunion]
        exact Set.mem_univ _
      simp only [Set.mem_union] at hmem
      rcases hmem with (((h1 | h2) | h3) | h4)
      · exact Or.inl (Or.inl ((hQ1 x hxO).mpr h1))
      · exact Or.inl (Or.inr ((hQ2 x hxO).mpr h2))
      · exact Or.inr (Or.inl ((hQ3 x hxO).mpr h3))
      · exact Or.inr (Or.inr ((hQ4 x hxO).mpr h4))

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
