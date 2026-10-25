import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra.Part2
open TateCechInfra
open SerreDualityTate SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology
open SerreDualityAnnihilator


/--
[IsCommensurable.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma IsCommensurable.refl
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W : Submodule k V} :
-- imply
  IsCommensurable W W := by
-- proof
  have h : Submodule.comap W.subtype (W ⊓ W) = ⊤ := by ext x; simp
  constructor <;> { rw [h]; infer_instance }

/--
[IsCommensurable.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma IsCommensurable.symm
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {W₁ W₂ : Submodule k V}
-- given
  (h : IsCommensurable W₁ W₂) :
-- imply
  IsCommensurable W₂ W₁ := by
-- proof
  constructor
  · rw [inf_comm]; exact h.2
  · rw [inf_comm]; exact h.1

namespace TateCechInfra

/--
[serre_duality_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma serre_duality_unconditional
  {k : Type*}
  [Field k]
  {k}
  {D : CechSheafData k} :
-- imply
  D.h0_EK = D.h1_E := by
-- proof
  unfold CechSheafData.h0_EK CechSheafData.h1_E
  exact_mod_cast tate_duality_core D.setup

end TateCechInfra

namespace TateCechInfra

/--
[serre_duality_h0_eq_h1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma serre_duality_h0_eq_h1
  {k : Type*}
  [Field k]
  {k}
  {D : CechSheafData k} :
-- imply
  D.h0_E = D.h1_EK := by
-- proof
  have h_tate := tate_duality_core D.setup
  have h_chi := serre_duality_chi_rank1 D.curve D.deg
  have hRR_E := D.hRR_E
  have hRR_EK := D.hRR_EK
  have h_cast : (Module.finrank k ↥D.setup.dual.cechH0 : ℤ) =
    (Module.finrank k D.setup.cechH1 : ℤ) := by exact_mod_cast h_tate
  linarith

end TateCechInfra

namespace TateCechInfra

/--
[serre_duality_both](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma serre_duality_both
  {k : Type*}
  [Field k]
  {k}
  {D : CechSheafData k} :
-- imply
  D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK :=
-- proof
  ⟨serre_duality_unconditional D, serre_duality_h0_eq_h1 D⟩

end TateCechInfra

namespace TateCechInfra

/--
[cech_data_feeds_tate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma cech_data_feeds_tate
  {k : Type*}
  [Field k]
  {k}
  {D : CechSheafData k} :
-- imply
  D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK :=
-- proof
  serre_duality_from_tate_both D.setup D.curve D.deg
    D.h0_E D.h1_E D.h0_EK D.h1_EK
    D.hRR_E D.hRR_EK rfl rfl

end TateCechInfra

namespace TateCechInfra

/--
[serre_duality_full_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma serre_duality_full_chain
  {k : Type*}
  [Field k]
  {k}
  {D : CechSheafData k} :
-- imply
  D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK ∧ D.curve.χ (1, D.deg) + D.curve.χ (1, D.curve.degK - D.deg) = 0 := by
-- proof
  exact ⟨serre_duality_unconditional D, serre_duality_h0_eq_h1 D,
    serre_duality_chi_rank1 D.curve D.deg⟩

end TateCechInfra

namespace TateCechInfra

/--
[residue_pairing_gives_annihilator_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma residue_pairing_gives_annihilator_inclusion
  {k : Type*}
  [Field k]
  {k}
  {S : TateDualitySetup k}
  {V₁' : Submodule k (Module.Dual k S.V)}
-- given
  (h_residue : ∀ f ∈ S.V₁, ∀ φ ∈ V₁', φ f = 0) :
-- imply
  V₁' ≤ S.V₁.dualAnnihilator :=
-- proof
  residue_implies_annihilator_inclusion k S V₁' h_residue

end TateCechInfra

namespace TateCechInfra

/--
[annihilator_equalities_give_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma annihilator_equalities_give_duality
  {k : Type*}
  [Field k]
  {k}
  {S : TateDualitySetup k}
  {V₁' V₂' : Submodule k (Module.Dual k S.V)}
-- given
  (h_eq₁ : V₁' = S.V₁.dualAnnihilator)
  (h_eq₂ : V₂' = S.V₂.dualAnnihilator) :
-- imply
  V₁' ⊓ V₂' = (S.V₁ ⊔ S.V₂).dualAnnihilator :=
-- proof
  annihilator_equality_gives_duality k S V₁' h_eq₁ V₂' h_eq₂

end TateCechInfra

namespace TateCechInfra

/--
[tate_dimension_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma tate_dimension_identity
  {k : Type*}
  [Field k]
  {k}
  {S : TateDualitySetup.{_, v} k}
  [FiniteDimensional k S.V] :
-- imply
  Module.finrank k ↥S.dual.cechH0 = Module.finrank k S.cechH1 :=
-- proof
  tate_duality_core S

end TateCechInfra

namespace TateCechInfra

/--
[annihilator_quotient_dimension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma annihilator_quotient_dimension
  {k : Type*}
  [Field k]
  {k}
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {W₁ W₂ : Submodule k V} :
-- imply
  Module.finrank k ↥(W₁ ⊔ W₂).dualAnnihilator = Module.finrank k (V ⧸ (W₁ ⊔ W₂)) := by
-- proof
  have h_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq (W₁ ⊔ W₂)
  have h_quot := Submodule.finrank_quotient_add_finrank (W₁ ⊔ W₂)
  omega

end TateCechInfra

namespace TateCechInfra

/--
[self_pairing_tate_duality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma self_pairing_tate_duality
  {k : Type*}
  [Field k]
  {k}
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : V ≃ₗ[k] Module.Dual k V}
  {W₁ W₂ : Submodule k V} :
-- imply
  Module.finrank k ↥(W₁.dualAnnihilator.comap B.toLinearMap ⊓ W₂.dualAnnihilator.comap B.toLinearMap) = Module.finrank k (V ⧸ (W₁ ⊔ W₂)) :=
-- proof
  tate_duality_via_pairing B W₁ W₂

end TateCechInfra

namespace TateCechInfra

/--
[genus_equality_from_serre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma genus_equality_from_serre
  {k : Type*}
  [Field k]
  {k}
  {C : SmoothCompleteCurve} :
-- imply
  C.χ (1, 0) + C.χ (1, C.degK) = 0 :=
-- proof
  genus_equality C

end TateCechInfra

namespace TateCechInfra

/--
[canonical_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma canonical_degree
  {k : Type*}
  [Field k]
  {k}
  {C : SmoothCompleteCurve} :
-- imply
  C.degK = 2 * C.g - 2 :=
-- proof
  deg_K_from_serre_duality C

end TateCechInfra

namespace TateCechInfra

/--
[serre_duality_direction_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean)
-/
@[path]
lemma serre_duality_direction_transfer
  {k : Type*}
  [Field k]
  {k}
  {C : SmoothCompleteCurve}
  {d : ℤ}
-- given
  (h0_E h1_E h0_EK h1_EK : ℤ)
  (hRR_E : h0_E - h1_E = C.χ (1, d))
  (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
  (hSD_one : h0_E = h1_EK) :
-- imply
  h1_E = h0_EK := by
-- proof
  have hchi := serre_duality_chi_rank1 C d
  linarith
end TateCechInfra



-- created on 2026-10-23
