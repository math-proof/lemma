import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityTate.Part3
open SerreDualityTate SerreDualityTate.TateDualitySetup
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology
open SerreDualityCurves


namespace SerreDualityTate.TateDualitySetup

/--
[cechH0_eq_inf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma cechH0_eq_inf
  {k : Type*}
  [Field k]
  {k}
  {S : TateDualitySetup k} :
-- imply
  S.cechH0 = S.V₁ ⊓ S.V₂ :=
-- proof
  rfl

end SerreDualityTate.TateDualitySetup

namespace SerreDualityTate

/--
[dual_H0_eq_annihilator_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma dual_H0_eq_annihilator_sup
  [Field k]
  {S : TateDualitySetup k} :
-- imply
  S.dual.cechH0 = (S.V₁ ⊔ S.V₂).dualAnnihilator := by
-- proof
  show S.V₁.dualAnnihilator ⊓ S.V₂.dualAnnihilator = (S.V₁ ⊔ S.V₂).dualAnnihilator
  exact (Submodule.dualAnnihilator_sup_eq S.V₁ S.V₂).symm

end SerreDualityTate

namespace SerreDualityTate

/--
[annihilator_inf_contains_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma annihilator_inf_contains_sup
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W₁ W₂ : Submodule k V} :
-- imply
  W₁.dualAnnihilator ⊔ W₂.dualAnnihilator ≤ (W₁ ⊓ W₂).dualAnnihilator :=
-- proof
  Submodule.sup_dualAnnihilator_le_inf W₁ W₂

end SerreDualityTate

namespace SerreDualityTate

/--
[annihilator_inf_eq_sup_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma annihilator_inf_eq_sup_field
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W₁ W₂ : Submodule k V} :
-- imply
  (W₁ ⊓ W₂).dualAnnihilator = W₁.dualAnnihilator ⊔ W₂.dualAnnihilator :=
-- proof
  Subspace.dualAnnihilator_inf_eq W₁ W₂

end SerreDualityTate

namespace SerreDualityTate

/--
[residue_annihilator_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma residue_annihilator_property
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {V₁ V₁' : Submodule k V}
  {φ : V →ₗ[k] Module.Dual k V}
-- given
  (h_zero : ∀ v ∈ V₁, ∀ w ∈ V₁', φ w v = 0) :
-- imply
  V₁' ≤ Submodule.comap φ V₁.dualAnnihilator := by
-- proof
  intro w hw
  simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  intro v hv
  exact h_zero v hv w hw

end SerreDualityTate

namespace SerreDualityTate

/--
[lattice_annihilator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma lattice_annihilator_nonneg
  [Field k]
  {f : ℤ →₀ k} :
-- imply
  (∀ g : ℤ →₀ k, (∀ (i : ℤ), i < 0 → g i = 0) → (∑ j ∈ f.support, f j * g (-1 - j)) = 0) → ∀ (i : ℤ), i < 0 → f i = 0 := by
-- proof
  intro hpair i hi
  specialize hpair (Finsupp.single (-1 - i) 1) (fun j hj => by
    simp only [Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · rfl)
  simp only [Finsupp.single_apply] at hpair
  have key : ∀ j ∈ f.support, f j * (if -1 - i = -1 - j then (1 : k) else 0) =
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

end SerreDualityTate

namespace SerreDualityTate

/--
[tate_H0_eq_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma tate_H0_eq_intersection
  [Field k]
  {S : TateDualitySetup k} :
-- imply
  S.cechH0 = S.V₁ ⊓ S.V₂ :=
-- proof
  rfl

end SerreDualityTate

namespace SerreDualityTate

/--
[tate_H0_dual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma tate_H0_dual_eq
  [Field k]
  {S : TateDualitySetup k} :
-- imply
  S.dual.cechH0 = (S.V₁ ⊔ S.V₂).dualAnnihilator :=
-- proof
  dual_H0_eq_annihilator_sup S

end SerreDualityTate

namespace SerreDualityTate

/--
[tate_duality_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma tate_duality_core
  [Field k]
  {S : TateDualitySetup k}
  [FiniteDimensional k S.V] :
-- imply
  Module.finrank k ↥S.dual.cechH0 = Module.finrank k S.cechH1 := by
-- proof
  unfold TateDualitySetup.cechH0 TateDualitySetup.dual TateDualitySetup.cechH1
  simp only
  rw [(Submodule.dualAnnihilator_sup_eq S.V₁ S.V₂).symm]
  have h_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq (S.V₁ ⊔ S.V₂)
  have h_quot := Submodule.finrank_quotient_add_finrank (S.V₁ ⊔ S.V₂)
  apply Nat.add_right_cancel (m := Module.finrank k ↥(S.V₁ ⊔ S.V₂))
  rw [add_comm (Module.finrank k ↥(S.V₁ ⊔ S.V₂).dualAnnihilator)]
  convert h_ann.trans h_quot.symm using 2

end SerreDualityTate

namespace SerreDualityTate

/--
[residue_characterization_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma residue_characterization_exact
  {k : Type*}
  [Field k]
  {n : ℤ}
  {a : k} :
-- imply
  SerreDualityCurves.residueMap k (Finsupp.single (n - 1) ((↑n : k) * a)) = 0 :=
-- proof
  SerreDualityCurves.residue_of_exact_zero k n a

end SerreDualityTate

namespace SerreDualityTate

/--
[residue_of_dt_over_t](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma residue_of_dt_over_t
  {k : Type*}
  [Field k] :
-- imply
  SerreDualityCurves.residueMap k (Finsupp.single (-1 : ℤ) (1 : k)) = 1 :=
-- proof
  SerreDualityCurves.residueMap_single_neg_one k 1

end SerreDualityTate

namespace SerreDualityTate

/--
[residue_pairing_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma residue_pairing_shift
  {k : Type*}
  [Field k]
  {i : ℤ}
  {a : k}
  {g : ℤ →₀ k} :
-- imply
  SerreDualityCurves.residuePairing k (Finsupp.single i a) g = a * g (SerreDualityP1.residueShift i) :=
-- proof
  SerreDualityCurves.residuePairing_via_shift k i a g

end SerreDualityTate

namespace SerreDualityTate

/--
[serre_duality_from_tate_both](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma serre_duality_from_tate_both
  {k : Type*}
  [Field k]
  [Field k]
  {S : TateDualitySetup k}
  [FiniteDimensional k S.V]
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_E h1_E h0_EK h1_EK : ℤ)
  (hRR_E : h0_E - h1_E = C.χ (1, d))
  (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
  (h_h0_EK : h0_EK = ↑(Module.finrank k ↥S.dual.cechH0))
  (h_h1_E : h1_E = ↑(Module.finrank k S.cechH1)) :
-- imply
  h0_EK = h1_E ∧ h0_E = h1_EK := by
-- proof
  have h_tate := tate_duality_core S
  have h_tate_int : (Module.finrank k ↥S.dual.cechH0 : ℤ) =
    (Module.finrank k S.cechH1 : ℤ) := by exact_mod_cast h_tate
  have h_first : h0_EK = h1_E := by
    rw [h_h0_EK, h_h1_E, h_tate_int]
  have hchi := SerreDualityCurves.serre_duality_chi_rank1 C d
  exact ⟨h_first, by linarith⟩

end SerreDualityTate

namespace SerreDualityTate

/--
[euler_char_dual_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma euler_char_dual_pair
  {k : Type*}
  [Field k]
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
-- proof
  SerreDualityCurves.serre_duality_chi_rank1 C d

end SerreDualityTate

namespace SerreDualityTate

/--
[euler_char_dual_pair_rank_r](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma euler_char_dual_pair_rank_r
  {k : Type*}
  [Field k]
  {C : SmoothCompleteCurve}
  {r d : ℤ} :
-- imply
  C.χ (r, d) + C.χ (r, r * C.degK - d) = 0 :=
-- proof
  SerreDualityCurves.serre_duality_chi_rank_r C r d

end SerreDualityTate

namespace SerreDualityTate

/--
[cechSetup_P1_H0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma cechSetup_P1_H0
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (cechSetup_P1 k n).cechH0 = CohomologyP1.NonNeg k ⊓ CohomologyP1.AtMost k n :=
-- proof
  rfl

end SerreDualityTate

namespace SerreDualityTate

/--
[serre_duality_P1_from_tate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma serre_duality_P1_from_tate
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < -1) :
-- imply
  Nonempty (((ℤ →₀ k) ⧸ (CohomologyP1.NonNeg k ⊔ CohomologyP1.AtMost k n)) ≃ₗ[k] ↥(CechH0 k (-2 - n))) :=
-- proof
  ⟨SerreDualityP1.serre_duality_P1 k n hn⟩

end SerreDualityTate

namespace SerreDualityTate

/--
[serre_duality_P1_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma serre_duality_P1_dim
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) :=
-- proof
  RiemannRoch.serre_duality_P1 k n

end SerreDualityTate

namespace SerreDualityTate

/--
[sum_of_residues_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma sum_of_residues_zero
  {k : Type*}
  [Field k]
  {n : ℕ}
  {c : Fin n → k}
  {a : Fin n → k}
-- given
  (hdist : Function.Injective a) :
-- imply
  (∑ i, ResidueSum.residuePartialFrac c a i) + ResidueSum.residueAtInfPartialFrac c a = 0 :=
-- proof
  ResidueSum.residue_sum_partial_frac c a hdist

end SerreDualityTate

namespace SerreDualityTate

/--
[residue_implies_annihilator_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma residue_implies_annihilator_inclusion
  {k : Type*}
  [Field k]
  {S : TateDualitySetup k}
  {V₁' : Submodule k (Module.Dual k S.V)}
-- given
  (h_residue : ∀ f ∈ S.V₁, ∀ φ ∈ V₁', φ f = 0) :
-- imply
  V₁' ≤ S.V₁.dualAnnihilator := by
-- proof
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator]
  exact fun v hv => h_residue v hv φ hφ

end SerreDualityTate

namespace SerreDualityTate

/--
[annihilator_equality_gives_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma annihilator_equality_gives_duality
  {k : Type*}
  [Field k]
  {S : TateDualitySetup k}
  {V₁' : Submodule k (Module.Dual k S.V)}
  {V₂' : Submodule k (Module.Dual k S.V)}
-- given
  (h_eq : V₁' = S.V₁.dualAnnihilator)
  (h_eq₂ : V₂' = S.V₂.dualAnnihilator) :
-- imply
  V₁' ⊓ V₂' = (S.V₁ ⊔ S.V₂).dualAnnihilator := by
-- proof
  rw [h_eq, h_eq₂]
  exact (Submodule.dualAnnihilator_sup_eq S.V₁ S.V₂).symm

end SerreDualityTate

namespace SerreDualityTate

/--
[serre_duality_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma serre_duality_full
  {C : SmoothCompleteCurve}
  {d : ℤ} :
-- imply
  C.χ (1, d) + C.χ (1, C.degK - d) = 0 ∧ C.χ (1, d) = d + 1 - C.g :=
-- proof
  SerreDualityCurves.serre_duality_theorem C d

end SerreDualityTate

namespace SerreDualityTate

/--
[genus_equality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma genus_equality
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, 0) + C.χ (1, C.degK) = 0 :=
-- proof
  SerreDualityCurves.serre_duality_chi_O_K C

end SerreDualityTate

namespace SerreDualityTate

/--
[riemann_roch_serre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma riemann_roch_serre
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_D h0_KD : ℤ)
  (hRR : h0_D - h0_KD = C.χ (1, d)) :
-- imply
  h0_D - h0_KD = d + 1 - C.g :=
-- proof
  SerreDualityCurves.riemann_roch_serre_form_general C d h0_D h0_KD hRR

end SerreDualityTate

namespace SerreDualityTate

/--
[deg_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma deg_canonical
  {C : SmoothCompleteCurve} :
-- imply
  C.degK = 2 * C.g - 2 :=
-- proof
  SerreDualityCurves.deg_K_from_serre_duality C

end SerreDualityTate

namespace SerreDualityTate

/--
[P1_serre_duality_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma P1_serre_duality_dim
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  RiemannRoch.dimH1 k n = RiemannRoch.dimH0 k (-2 - n) :=
-- proof
  RiemannRoch.serre_duality_P1 k n

end SerreDualityTate

namespace SerreDualityTate

/--
[P1_riemann_roch](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma P1_riemann_roch
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (RiemannRoch.dimH0 k n : ℤ) - (RiemannRoch.dimH1 k n : ℤ) = n + 1 :=
-- proof
  RiemannRoch.riemann_roch_P1 k n

end SerreDualityTate

namespace SerreDualityTate

/--
[P1_serre_duality_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityTate.lean)
-/
@[path]
lemma P1_serre_duality_equiv
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < -1) :
-- imply
  Module.finrank k ((ℤ →₀ k) ⧸ (CohomologyP1.NonNeg k ⊔ CohomologyP1.AtMost k n)) = Module.finrank k ↥(CechH0 k (-2 - n)) :=
-- proof
  SerreDualityP1.serre_duality_finrank k n hn
end SerreDualityTate



-- created on 2026-10-23
