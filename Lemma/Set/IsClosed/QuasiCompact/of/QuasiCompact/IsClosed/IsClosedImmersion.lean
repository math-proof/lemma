import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact.lean)
-/
@[main]
private lemma main
  {B E P : Scheme.{u}}
  {m : E ⟶ P}
  {πP : P ⟶ B}
  {ι : Type v} [Finite ι]
  {W : ι → P.Opens}
-- given
  (hm : IsClosedImmersion m)
  (hW : IsClosed ((⨅ j, W j : P.Opens) : Set P))
  (hW' : QuasiCompact ((⨅ j, W j).ι ≫ πP)) :
-- imply
  IsClosed ((⨅ j, m ⁻¹ᵁ (W j) : E.Opens) : Set E) ∧
      QuasiCompact ((⨅ j, m ⁻¹ᵁ (W j)).ι ≫ m ≫ πP) := by
-- proof
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have coe_iInf : ∀ {Z : Scheme.{u}} (V : ι → Z.Opens),
      ((⨅ j, V j : Z.Opens) : Set Z) = ⋂ j, (V j : Set Z) := by
    intro Z V
    rw [← Finset.inf_univ_eq_iInf, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_univ_eq_iInf,
      Set.iInf_eq_iInter]
    rfl
  have key : (⨅ j, m ⁻¹ᵁ (W j)) = m ⁻¹ᵁ (⨅ j, W j) := by
    apply TopologicalSpace.Opens.ext
    rw [coe_iInf, Scheme.Hom.coe_preimage, coe_iInf, Set.preimage_iInter]
    rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · rw [Scheme.Hom.coe_preimage]
    exact hW.preimage m.continuous
  · have h : (m ⁻¹ᵁ (⨅ j, W j)).ι ≫ m ≫ πP = (m ∣_ (⨅ j, W j)) ≫ (⨅ j, W j).ι ≫ πP := by
      rw [← Category.assoc (m ∣_ _), morphismRestrict_ι, Category.assoc]
    rw [h]
    have := hm
    have := hW'
    infer_instance


-- created on 2026-10-05
