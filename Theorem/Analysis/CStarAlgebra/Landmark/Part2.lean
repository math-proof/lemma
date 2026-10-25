/-
  Author: @toskua, Avocado
-/
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic.Positivity
import Def.Analysis.CStarAlgebra.Landmark.Part2


section

open scoped InnerProductSpace ComplexOrder

universe u

namespace Analysis.CStarAlgebra.LandmarkWanted

/-- Key analytic input: for `c ≠ 0` there is a positive linear functional attaining the
norm at `star c * c`. -/
theorem exists_posMap_norm (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (c : A) (hc : c ≠ 0) :
    ∃ f : A →ₚ[ℂ] ℂ, f (star c * c) = ((‖star c * c‖ : ℝ) : ℂ) := by
  classical
  set b : A := star c * c with hb_def
  have hb_nn : 0 ≤ b := star_mul_self_nonneg c
  have hb_sa : IsSelfAdjoint b := IsSelfAdjoint.star_mul_self c
  have hb_ne : b ≠ 0 := by
    intro h0
    apply hc
    have h1 : ‖c‖ * ‖c‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, ← hb_def, h0, norm_zero]
    have h2 : ‖c‖ = 0 := mul_self_eq_zero.mp h1
    exact norm_eq_zero.mp h2
  have : Nontrivial A := ⟨c, 0, hc⟩
  have : IsStarNormal b := IsStarNormal.mk (by rw [hb_sa])
  have hmemR : ‖b‖ ∈ spectrum ℝ b :=
    CStarAlgebra.norm_mem_spectrum_of_nonneg b hb_nn
  have hmemC : ((‖b‖ : ℝ) : ℂ) ∈ spectrum ℂ b :=
    (IsSelfAdjoint.coe_mem_spectrum_complex hb_sa).mpr hmemR
  obtain ⟨χ, hχ⟩ := (StarAlgebra.elemental.bijective_characterSpaceToSpectrum b).2
    ⟨((‖b‖ : ℝ) : ℂ), hmemC⟩
  have hχb : χ ⟨b, StarAlgebra.elemental.self_mem ℂ b⟩ = ((‖b‖ : ℝ) : ℂ) :=
    congrArg Subtype.val hχ
  set S : StarSubalgebra ℂ A := StarAlgebra.elemental ℂ b with hS_def
  have hSnt : Nontrivial ↥S := by
    refine ⟨⟨b, StarAlgebra.elemental.self_mem ℂ b⟩, 0, ?_⟩
    intro h
    apply hb_ne
    have h2 := Subtype.ext_iff.mp h
    simpa using h2
  set p : Subspace ℂ A := Subalgebra.toSubmodule S.toSubalgebra with hp_def
  obtain ⟨g, hg_ext, hg_norm⟩ :=
    exists_extension_norm_eq p (WeakDual.CharacterSpace.toCLM χ)
  have hEq : WeakDual.CharacterSpace.toCLM χ
      = WeakDual.toStrongDual (↑χ : WeakDual ℂ ↥S) := by
    ext x
    rfl
  have hle : ‖WeakDual.toStrongDual (↑χ : WeakDual ℂ ↥S)‖ ≤ ‖(1 : ↥S)‖ :=
    WeakDual.CharacterSpace.norm_le_norm_one χ
  have h1 : (‖(1 : ↥S)‖) = 1 := norm_one
  have hle2 : ‖WeakDual.CharacterSpace.toCLM χ‖ ≤ 1 := by
    rw [hEq]
    exact hle.trans_eq h1
  have hg1 : g 1 = 1 := by
    have hmem : (1 : A) ∈ p := by
      change (1 : A) ∈ Subalgebra.toSubmodule S.toSubalgebra
      rw [Subalgebra.mem_toSubmodule]
      exact OneMemClass.one_mem S
    have h := hg_ext ⟨(1 : A), hmem⟩
    have h2 : g 1 = χ ⟨(1 : A), hmem⟩ := by simpa using h
    exact h2.trans (map_one χ)
  have hgnorm : ‖g‖ = 1 := by
    apply le_antisymm _ _
    · rw [hg_norm]
      exact hle2
    · have h := g.le_opNorm (1 : A)
      rw [hg1, norm_one] at h
      simpa using h
  have hmon : Monotone ⇑g :=
    ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.mpr (by simp [hgnorm, hg1])
  have hmemSb : b ∈ p := by
    change b ∈ Subalgebra.toSubmodule S.toSubalgebra
    rw [Subalgebra.mem_toSubmodule]
    exact StarAlgebra.elemental.self_mem ℂ b
  have hgb : g b = ((‖b‖ : ℝ) : ℂ) := by
    have hval : WeakDual.CharacterSpace.toCLM χ (⟨b, hmemSb⟩ : ↥p)
        = ((‖b‖ : ℝ) : ℂ) := by
      rw [WeakDual.CharacterSpace.coe_toCLM]
      exact hχb
    have hbb : g b = WeakDual.CharacterSpace.toCLM χ (⟨b, hmemSb⟩ : ↥p) :=
      hg_ext ⟨b, hmemSb⟩
    exact hbb.trans hval
  refine ⟨PositiveLinearMap.mk g.toLinearMap (by exact hmon), ?_⟩
  exact hgb

/-- Componentwise action of `repHom`. -/
theorem repHom_apply (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (a : A) (x : UH A) (f : A →ₚ[ℂ] ℂ) :
    ((repHom A a) x) f = f.gnsStarAlgHom a (x f) :=
  repOp_apply A a x f

/-- The universal representation kills only zero. -/
theorem repHom_eq_zero (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (c : A) (hc : repHom A c = 0) : c = 0 := by
  classical
  by_cases hc0 : c = 0
  · exact hc0
  · obtain ⟨f, hf⟩ := exists_posMap_norm A c hc0
    have h0 : ((repHom A c) (lp.single 2 f (↑(f.toPreGNS 1) : f.GNS))) f = 0 := by
      rw [hc]
      simp
    rw [repHom_apply, lp.single_apply_self] at h0
    have h1 : f.gnsStarAlgHom c (↑(f.toPreGNS 1) : f.GNS)
        = (↑(f.toPreGNS c) : f.GNS) := by
      change f.gnsNonUnitalStarAlgHom c (↑(f.toPreGNS 1) : f.GNS) = _
      rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,
        PositiveLinearMap.leftMulMapPreGNS_apply,
        PositiveLinearMap.ofPreGNS_toPreGNS, mul_one]
    rw [h1] at h0
    have hnorm0 : ‖(↑(f.toPreGNS c) : f.GNS)‖ = 0 := by
      rw [h0]
      exact norm_zero
    have hpre : ‖f.toPreGNS c‖ = 0 := by
      have h := UniformSpace.Completion.norm_coe (f.toPreGNS c)
      rw [hnorm0] at h
      exact h.symm
    have hfb0 : f (star c * c) = 0 := by
      have hsq := PositiveLinearMap.preGNS_norm_sq f (f.toPreGNS c)
      rw [PositiveLinearMap.ofPreGNS_toPreGNS, hpre] at hsq
      simpa using hsq.symm
    have hnormb : ‖star c * c‖ = 0 := by
      have h : ((‖star c * c‖ : ℝ) : ℂ) = 0 := hf.symm.trans hfb0
      simpa using h
    have hbb0 : star c * c = 0 := norm_eq_zero.mp hnormb
    have hcc : ‖c‖ * ‖c‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, hbb0, norm_zero]
    have hcn : ‖c‖ = 0 := mul_self_eq_zero.mp hcc
    exact absurd (norm_eq_zero.mp hcn) hc0

/-- The universal representation is injective. -/
theorem repHom_injective (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Function.Injective (repHom A) := by
  intro x y hxy
  have h0 : repHom A (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hxy0 : x - y = 0 := repHom_eq_zero A _ h0
  exact sub_eq_zero.mp hxy0

set_option linter.unusedVariables false in
/--
Every C*-algebra `A` admits an isometric injective `∗`-homomorphism `π : A →⋆ₐ[ℂ] B(H)` into
bounded operators on some complex Hilbert space `H`. Source: Gelfand–Naimark theorem, I. M.
Gelfand–M. A. Naimark, Mat. Sb. 12 (1943); see Murphy, C*-Algebras and Operator Theory, A Course
in Operator Theory; Lean is isometric injective star-homomorphism into B(H) form.

Proves `Wanted` entry `cStarAlgebra_gelfandNaimark`.
-/
theorem cStarAlgebra_gelfandNaimark
    (A : Type u) [CStarAlgebra A] :
    ∃ (H : Type u) (hH1 : NormedAddCommGroup H)
      (hH2 : InnerProductSpace ℂ H) (hH3 : CompleteSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective π ∧ ∀ a : A, ‖π a‖ = ‖a‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  exact ⟨UH A, inferInstance, inferInstance, inferInstance, repHom A,
    repHom_injective A,
    fun a => NonUnitalStarAlgHom.norm_map (repHom A) (repHom_injective A) a⟩

end Analysis.CStarAlgebra.LandmarkWanted
end
