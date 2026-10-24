import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SerreDualityAnnihilator
open SerreDualityAnnihilator
open SerreDualityTate SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology
open Module FiniteDimensional Submodule


namespace SerreDualityAnnihilator

/--
[annihilator_nonneg_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma annihilator_nonneg_reverse
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  (∀ (i : ℤ), i < 0 → f i = 0) → (∀ g : ℤ →₀ k, (∀ (i : ℤ), i < 0 → g i = 0) → (∑ j ∈ f.support, f j * g (-1 - j)) = 0) := by
-- proof
  intro hf g hg
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hj0 : j < 0
  · simp [hf j hj0]
  · push Not at hj0
    have h_neg : -1 - j < 0 := by omega
    simp [hg (-1 - j) h_neg]

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[annihilator_nonneg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma annihilator_nonneg_iff
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  (∀ g : ℤ →₀ k, (∀ (i : ℤ), i < 0 → g i = 0) → (∑ j ∈ f.support, f j * g (-1 - j)) = 0) ↔ (∀ (i : ℤ), i < 0 → f i = 0) :=
-- proof
  ⟨SerreDualityTate.lattice_annihilator_nonneg f,
    annihilator_nonneg_reverse f⟩

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[strictly_neg_annihilates_strictly_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma strictly_neg_annihilates_strictly_neg
  [Field k]
  {f : ℤ →₀ k}
-- given
  (hf : ∀ (i : ℤ), 0 ≤ i → f i = 0) :
-- imply
  ∀ g : ℤ →₀ k, (∀ (i : ℤ), 0 ≤ i → g i = 0) → (∑ j ∈ g.support, g j * f (-1 - j)) = 0 := by
-- proof
  intro g hg
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hj0 : 0 ≤ j
  · simp [hg j hj0]
  · push Not at hj0
    have h_nonneg : 0 ≤ -1 - j := by omega
    simp [hf (-1 - j) h_nonneg]

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[annihilator_strictly_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma annihilator_strictly_neg
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  (∀ g : ℤ →₀ k, (∀ (i : ℤ), 0 ≤ i → g i = 0) → (∑ j ∈ g.support, g j * f (-1 - j)) = 0) → ∀ (i : ℤ), 0 ≤ i → f i = 0 := by
-- proof
  intro hpair i hi
  specialize hpair (Finsupp.single (-1 - i) 1) (fun j hj => by
    simp only [Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · rfl)
  have hsupp : (Finsupp.single (-1 - i) (1 : k)).support = {-1 - i} := by
    rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  rw [hsupp, Finset.sum_singleton] at hpair
  simp only [Finsupp.single_apply, ↓reduceIte, one_mul,
    show (-1 : ℤ) - (-1 - i) = i from by omega] at hpair
  exact hpair

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[annihilator_strictly_neg_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma annihilator_strictly_neg_iff
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  (∀ g : ℤ →₀ k, (∀ (i : ℤ), 0 ≤ i → g i = 0) → (∑ j ∈ g.support, g j * f (-1 - j)) = 0) ↔ (∀ (i : ℤ), 0 ≤ i → f i = 0) :=
-- proof
  ⟨annihilator_strictly_neg f,
    strictly_neg_annihilates_strictly_neg f⟩
section TateDualitySelfDual
variable {k : Type*} [Field k]
open Module FiniteDimensional Submodule

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[tate_duality_via_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma tate_duality_via_pairing
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : V ≃ₗ[k] Module.Dual k V}
  {W₁ W₂ : Submodule k V} :
-- imply
  finrank k ↥(W₁.dualAnnihilator.comap B.toLinearMap ⊓ W₂.dualAnnihilator.comap B.toLinearMap) = finrank k (V ⧸ (W₁ ⊔ W₂)) := by
-- proof
  rw [← Submodule.comap_inf, ← Submodule.dualAnnihilator_sup_eq]
  have h_eq : Submodule.map B.toLinearMap
    ((W₁ ⊔ W₂).dualAnnihilator.comap B.toLinearMap) =
    (W₁ ⊔ W₂).dualAnnihilator :=
    Submodule.map_comap_eq_of_surjective B.surjective _
  have h_finrank : finrank k ↥((W₁ ⊔ W₂).dualAnnihilator.comap B.toLinearMap) =
    finrank k ↥(W₁ ⊔ W₂).dualAnnihilator :=
    LinearEquiv.finrank_eq ((B.submoduleMap _).trans (LinearEquiv.ofEq _ _ h_eq))
  rw [h_finrank]
  have h_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq (W₁ ⊔ W₂)
  have h_quot := Submodule.finrank_quotient_add_finrank (W₁ ⊔ W₂)
  omega

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[tate_duality_via_self_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma tate_duality_via_self_duality
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : V ≃ₗ[k] Module.Dual k V}
  {W₁ W₂ W₁' W₂' : Submodule k V}
-- given
  (h₁ : W₁' = W₁.dualAnnihilator.comap B.toLinearMap)
  (h₂ : W₂' = W₂.dualAnnihilator.comap B.toLinearMap) :
-- imply
  finrank k ↥(W₁' ⊓ W₂') = finrank k (V ⧸ (W₁ ⊔ W₂)) := by
-- proof
  subst h₁; subst h₂
  exact tate_duality_via_pairing B W₁ W₂

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[tate_euler_char_self_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma tate_euler_char_self_dual
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {W₁ W₂ : Submodule k V} :
-- imply
  (finrank k ↥(W₁ ⊓ W₂) : ℤ) - finrank k (V ⧸ (W₁ ⊔ W₂)) = finrank k W₁ + finrank k W₂ - finrank k V := by
-- proof
  have h := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  have hq := Submodule.finrank_quotient_add_finrank (W₁ ⊔ W₂)
  omega

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[tate_duality_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma tate_duality_symmetric
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : V ≃ₗ[k] Module.Dual k V}
  {W₁ W₂ W₁' W₂' : Submodule k V}
-- given
  (h₁ : W₁' = W₁.dualAnnihilator.comap B.toLinearMap)
  (h₂ : W₂' = W₂.dualAnnihilator.comap B.toLinearMap) :
-- imply
  (finrank k ↥(W₁ ⊓ W₂) : ℤ) + finrank k ↥(W₁' ⊓ W₂') = finrank k W₁ + finrank k W₂ - finrank k V + 2 * finrank k (V ⧸ (W₁ ⊔ W₂)) := by
-- proof
  have htate := tate_duality_via_self_duality B W₁ W₂ W₁' W₂' h₁ h₂
  have heuler := tate_euler_char_self_dual W₁ W₂
  omega

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[shift_realizes_tate_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma shift_realizes_tate_duality
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < -1) :
-- imply
  Module.finrank k ((ℤ →₀ k) ⧸ (CohomologyP1.NonNeg k ⊔ CohomologyP1.AtMost k n)) = Module.finrank k ↥(CechH0 k (-2 - n)) :=
-- proof
  SerreDualityP1.serre_duality_finrank k n hn

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[serre_duality_P1_both_directions](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma serre_duality_P1_both_directions
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) ∧ RiemannRoch.dimH0 k n = RiemannRoch.dimH1 k (-2 - n) := by
-- proof
  constructor
  · exact RiemannRoch.serre_duality_P1 k n
  · have h := RiemannRoch.serre_duality_P1 k (-2 - n)
    have heq : -2 - (-2 - n) = n := by omega
    rwa [heq] at h

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[serre_duality_chain_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma serre_duality_chain_P1
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) ∧ RiemannRoch.dimH0 k n = RiemannRoch.dimH1 k (-2 - n) ∧ (RiemannRoch.dimH0 k n : ℤ) - (RiemannRoch.dimH1 k n : ℤ) = n + 1 := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · exact (serre_duality_P1_both_directions k n).1
  · exact (serre_duality_P1_both_directions k n).2
  · exact RiemannRoch.riemann_roch_P1 k n

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[serre_duality_general_strategy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma serre_duality_general_strategy
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
-- proof
  SerreDualityCurves.serre_duality_chi_rank1 C d

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[abstract_matches_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma abstract_matches_P1
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  RiemannRoch.dimH0 k (-2 - n) = RiemannRoch.dimH1 k n :=
-- proof
  (RiemannRoch.serre_duality_P1 k n).symm

end SerreDualityAnnihilator

namespace SerreDualityAnnihilator

/--
[tate_applied_to_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityAnnihilator.lean)
-/
@[path]
lemma tate_applied_to_P1
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < -1) :
-- imply
  Module.finrank k (SerreDualityTate.cechSetup_P1 k n).cechH1 = Module.finrank k ↥(CechH0 k (-2 - n)) :=
-- proof
  SerreDualityP1.serre_duality_finrank k n hn
end SerreDualityAnnihilator



-- created on 2026-10-23
