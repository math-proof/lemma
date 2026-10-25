import Mathlib
import sympy.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.TateResidueOrthogonality
open TateResidueOrthogonality
open SerreDualityTate SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology
open SerreDualityAnnihilator TateCechInfra


namespace TateResidueOrthogonality

/--
[residue_pairing_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma residue_pairing_nondegenerate
  [Field k]
  {f : ℤ →₀ k}
-- given
  (hpair : ∀ g : ℤ →₀ k, (∑ j ∈ f.support, f j * g (-1 - j)) = 0) :
-- imply
  f = 0 := by
-- proof
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  specialize hpair (Finsupp.single (-1 - i) 1)
  simp only [Finsupp.single_apply] at hpair
  have key : ∀ j ∈ f.support,
    f j * (if -1 - i = -1 - j then (1 : k) else 0) =
    if j = i then f j else 0 := by
    intro j _
    split_ifs with h1 h2
    · simp
    · omega
    · omega
    · simp
  rw [Finset.sum_congr rfl key] at hpair
  by_cases hm : i ∈ f.support
  · rw [Finset.sum_ite_eq' f.support i] at hpair
    simp [hm] at hpair
    exact hpair
  · exact Finsupp.notMem_support_iff.mp hm

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[residue_pairing_nondegenerate_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma residue_pairing_nondegenerate_right
  [Field k]
  {g : ℤ →₀ k}
-- given
  (hpair : ∀ f : ℤ →₀ k, (∑ j ∈ f.support, f j * g (-1 - j)) = 0) :
-- imply
  g = 0 := by
-- proof
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  have h := hpair (Finsupp.single (-1 - i) 1)
  simp only [Finsupp.single_apply, Finsupp.support_single_ne_zero _ one_ne_zero,
    Finset.sum_singleton] at h
  have : -1 - (-1 - i) = i := by omega
  rw [this] at h
  simpa using h

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[nonneg_annihilates_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma nonneg_annihilates_nonneg
  [Field k]
  {f : ℤ →₀ k}
  {g : ℤ →₀ k}
-- given
  (hf : ∀ i, i < 0 → f i = 0)
  (hg : ∀ i, i < 0 → g i = 0) :
-- imply
  (∑ j ∈ f.support, f j * g (-1 - j)) = 0 := by
-- proof
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj_neg : j < 0
  · simp [hf j hj_neg]
  · have : -1 - j < 0 := by omega
    simp [hg (-1 - j) this]

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[lattice_annihilator_nonneg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma lattice_annihilator_nonneg_iff
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  (∀ g : ℤ →₀ k, (∀ i, i < 0 → g i = 0) → (∑ j ∈ f.support, f j * g (-1 - j)) = 0) ↔ (∀ i, i < 0 → f i = 0) := by
-- proof
  constructor
  · exact lattice_annihilator_nonneg f
  · intro hf g hg
    exact nonneg_annihilates_nonneg f hf g hg

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[discrete_cocompact_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma discrete_cocompact_dual
  {k : Type*}
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {W Λ : Submodule k V}
  {_ : IsArithmeticallyDiscrete k W Λ}
  {_ : IsArithmeticallyCocompact k W Λ} :
-- imply
  IsArithmeticallyDiscrete k W.dualAnnihilator Λ.dualAnnihilator ∧ IsArithmeticallyCocompact k W.dualAnnihilator Λ.dualAnnihilator := by
-- proof
  exact ⟨⟨Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)⟩,
    ⟨Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)⟩⟩

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[annihilator_finiteDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma annihilator_finiteDim
  {k : Type*}
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {W : Submodule k V} :
-- imply
  FiniteDimensional k W.dualAnnihilator :=
-- proof
  inferInstance

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[inclusion_to_equality_by_dimension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma inclusion_to_equality_by_dimension
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W₁ W₂ : Submodule k V}
  [FiniteDimensional k W₂]
-- given
  (h_le : W₁ ≤ W₂)
  (h_dim : Module.finrank k W₁ = Module.finrank k W₂) :
-- imply
  W₁ = W₂ :=
-- proof
  Submodule.eq_of_le_of_finrank_eq h_le h_dim

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[annihilator_equality_from_inclusion_and_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma annihilator_equality_from_inclusion_and_dim
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {V₁ : Submodule k V}
  {V₁' : Submodule k (Module.Dual k V)}
  [FiniteDimensional k V₁.dualAnnihilator]
-- given
  (h_inc : V₁' ≤ V₁.dualAnnihilator)
  (h_dim : Module.finrank k V₁' = Module.finrank k V₁.dualAnnihilator) :
-- imply
  V₁' = V₁.dualAnnihilator :=
-- proof
  Submodule.eq_of_le_of_finrank_eq h_inc h_dim

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[tate_orthogonality_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma tate_orthogonality_complete
  [Field k]
  {S : TateDualitySetup k}
  [FiniteDimensional k S.V]
  {V₁' V₂' : Submodule k (Module.Dual k S.V)}
-- given
  (h_V1_eq : V₁' = S.V₁.dualAnnihilator)
  (h_V2_eq : V₂' = S.V₂.dualAnnihilator) :
-- imply
  V₁' ⊓ V₂' = (S.V₁ ⊔ S.V₂).dualAnnihilator ∧ Module.finrank k ↥(V₁' ⊓ V₂') = Module.finrank k (S.V ⧸ (S.V₁ ⊔ S.V₂)) := by
-- proof
  constructor
  · rw [h_V1_eq, h_V2_eq]
    exact (Submodule.dualAnnihilator_sup_eq S.V₁ S.V₂).symm
  · rw [h_V1_eq, h_V2_eq, (Submodule.dualAnnihilator_sup_eq S.V₁ S.V₂).symm]
    have h_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq (S.V₁ ⊔ S.V₂)
    have h_quot := Submodule.finrank_quotient_add_finrank (S.V₁ ⊔ S.V₂)
    omega

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[tate_orthogonality_gives_serre_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma tate_orthogonality_gives_serre_duality
  [Field k]
  {S : TateDualitySetup k}
  [FiniteDimensional k S.V]
  {V₁' V₂' : Submodule k (Module.Dual k S.V)}
-- given
  (h_V1_eq : V₁' = S.V₁.dualAnnihilator)
  (h_V2_eq : V₂' = S.V₂.dualAnnihilator) :
-- imply
  Module.finrank k ↥(V₁' ⊓ V₂') = Module.finrank k S.cechH1 :=
-- proof
  (tate_orthogonality_complete S V₁' V₂' h_V1_eq h_V2_eq).2

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[tate_serre_duality_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma tate_serre_duality_chain
  [Field k]
  {S : TateDualitySetup k}
  [FiniteDimensional k S.V]
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_E h1_EK : ℤ)
  (hRR_E : h0_E - ↑(Module.finrank k S.cechH1) = C.χ (1, d))
  (hRR_EK : ↑(Module.finrank k ↥S.dual.cechH0) - h1_EK = C.χ (1, C.degK - d)) :
-- imply
  h0_E = h1_EK := by
-- proof
  have h_tate := tate_duality_core S
  have h_chi := SerreDualityCurves.serre_duality_chi_rank1 C d
  have h_cast : (Module.finrank k ↥S.dual.cechH0 : ℤ) =
    (Module.finrank k S.cechH1 : ℤ) := by exact_mod_cast h_tate
  linarith

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[residue_pairing_separating](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma residue_pairing_separating
  [Field k]
  {f : ℤ →₀ k}
-- given
  (hf : f ≠ 0) :
-- imply
  ∃ g : ℤ →₀ k, (∑ j ∈ f.support, f j * g (-1 - j)) ≠ 0 := by
-- proof
  by_contra h
  push Not at h
  exact hf (residue_pairing_nondegenerate f h)

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[residue_dual_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma residue_dual_basis
  [Field k]
  {i : ℤ} :
-- imply
  (∑ j ∈ (Finsupp.single i (1 : k)).support, (Finsupp.single i (1 : k)) j * (Finsupp.single (-1 - i) (1 : k)) (-1 - j)) = (1 : k) := by
-- proof
  simp only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_apply]
  simp

end TateResidueOrthogonality

namespace TateResidueOrthogonality

/--
[residue_dual_basis_orthog](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateResidueOrthogonality.lean)
-/
@[path]
lemma residue_dual_basis_orthog
  [Field k]
  {i j : ℤ}
-- given
  (hij : i ≠ j) :
-- imply
  (∑ l ∈ (Finsupp.single i (1 : k)).support, (Finsupp.single i (1 : k)) l * (Finsupp.single (-1 - j) (1 : k)) (-1 - l)) = (0 : k) := by
-- proof
  simp only [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_apply]
  simp [show -1 - j ≠ -1 - i from by omega]
end TateResidueOrthogonality



-- created on 2026-10-23
