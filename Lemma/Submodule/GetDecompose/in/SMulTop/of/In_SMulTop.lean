import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Ideal.GetDecompose.in.AugmentationIdealGraded.of.In_AugmentationIdealGraded
import Lemma.Submodule.GetDecompose_SMul.in.SMulTop.of.In.In_Aug
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Graded components of an augmentation-ideal multiple stay in that multiple
(atlas aug_smul_graded_component).

[aug_smul_graded_component](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  [CommRing S]
  [Algebra k S]
  [AddCommGroup M]
  [Module S M]
  [Module k M]
  [IsScalarTower k S M]
  {𝒮 : ℕ → Submodule k S} [GradedAlgebra 𝒮]
  {ℳ : ℕ → Submodule k M} [DirectSum.Decomposition ℳ]
  {d : ℕ}
  {z : M}
-- given
  (hsmul : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j))
  (hz : z ∈ (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M)) :
-- imply
  (↑((DirectSum.decompose ℳ z) d) : M) ∈ (Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) • (⊤ : Submodule S M) := by
-- proof
  classical
  refine Submodule.smul_induction_on hz ?_ ?_
  ·
    intro r hr n _
    have h_eq_r : ((DirectSum.decompose ℳ (r • n)) d : M) =
      ∑ j ∈ (DirectSum.decompose 𝒮 r).support,
        ((DirectSum.decompose ℳ (((DirectSum.decompose 𝒮 r) j : S) • n)) d : M) := by
      conv_lhs =>
        rw [show r • n = ∑ j ∈ (DirectSum.decompose 𝒮 r).support,
          ((DirectSum.decompose 𝒮 r) j : S) • n by
          conv_lhs => rw [← DirectSum.sum_support_decompose 𝒮 r]; rw [Finset.sum_smul]]
      rw [DirectSum.decompose_sum]; simp
    rw [h_eq_r]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.GetDecompose_SMul.in.SMulTop.of.In.In_Aug (𝒮 := 𝒮) (ℳ := ℳ) hsmul
      ((DirectSum.decompose 𝒮 r) j).2
    exact Ideal.GetDecompose.in.AugmentationIdealGraded.of.In_AugmentationIdealGraded (𝒮 := 𝒮) (j := j) hr
  ·
    intro x y hx hy
    rw [DirectSum.decompose_add]
    simp only [DirectSum.add_apply, AddMemClass.coe_add]
    exact Submodule.add_mem _ hx hy


-- created on 2026-10-24
