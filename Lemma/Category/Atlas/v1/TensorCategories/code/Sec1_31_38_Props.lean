import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiBialgebra
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
open CategoryTheory
open scoped TensorProduct


namespace TensorCategories

/--
[prop_1_34_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Sec1_31_38_Props.lean)
-/
@[path]
lemma prop_1_34_4
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [hQB : QuasiBialgebra R H] :
-- imply
  (∀ a : H, QuasiBialgebra.idTensorComul R H hQB.comul a * (hQB.Φ : H ⊗[R] (H ⊗[R] H)) = (hQB.Φ : H ⊗[R] (H ⊗[R] H)) * QuasiBialgebra.comulTensorId R H hQB.comul a) ∧ ((1 : H) ⊗ₜ[R] (hQB.Φ : H ⊗[R] (H ⊗[R] H)) * QuasiBialgebra.idComulId R H hQB.comul (hQB.Φ : H ⊗[R] (H ⊗[R] H)) * QuasiBialgebra.embedPhiRight R H (hQB.Φ : H ⊗[R] (H ⊗[R] H)) = QuasiBialgebra.idIdComul R H hQB.comul (hQB.Φ : H ⊗[R] (H ⊗[R] H)) * QuasiBialgebra.comulIdId R H hQB.comul (hQB.Φ : H ⊗[R] (H ⊗[R] H))) ∧ ((Algebra.TensorProduct.lid R H).toAlgHom.comp ((Algebra.TensorProduct.map hQB.counit (AlgHom.id R H)).comp hQB.comul) = AlgHom.id R H) ∧ ((Algebra.TensorProduct.rid R R H).toAlgHom.comp ((Algebra.TensorProduct.map (AlgHom.id R H) hQB.counit).comp hQB.comul) = AlgHom.id R H) ∧ (QuasiBialgebra.idCounitId R H hQB.counit (hQB.Φ : H ⊗[R] (H ⊗[R] H)) = 1) :=
-- proof
  ⟨hQB.quasi_coassoc, hQB.pentagon, hQB.left_counit, hQB.right_counit, hQB.Φ_counit⟩

end TensorCategories

namespace TensorCategories

/--
[prop_1_35_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Sec1_31_38_Props.lean)
-/
@[path]
lemma prop_1_35_1
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [hQH : QuasiHopfAlgebra R H] :
-- imply
  QuasiBialgebra.phiBetaSAlphaMap R H hQH.S.toLinearMap hQH.α_elem hQH.β_elem (hQH.Φ : H ⊗[R] (H ⊗[R] H)) = 1 ∧ QuasiBialgebra.phiInvSAlphaBetaSMap R H hQH.S.toLinearMap hQH.α_elem hQH.β_elem (↑hQH.Φ⁻¹ : H ⊗[R] (H ⊗[R] H)) = 1 :=
-- proof
  ⟨hQH.phi_beta_S_alpha, hQH.phiInv_S_alpha_beta_S⟩

end TensorCategories

namespace TensorCategories

/--
[Proposition_1_35_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Sec1_31_38_Props.lean)
-/
@[path]
lemma Proposition_1_35_1
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [hQH : QuasiHopfAlgebra R H] :
-- imply
  QuasiBialgebra.phiBetaSAlphaMap R H hQH.S.toLinearMap hQH.α_elem hQH.β_elem (hQH.Φ : H ⊗[R] (H ⊗[R] H)) = 1 ∧ QuasiBialgebra.phiInvSAlphaBetaSMap R H hQH.S.toLinearMap hQH.α_elem hQH.β_elem (↑hQH.Φ⁻¹ : H ⊗[R] (H ⊗[R] H)) = 1 :=
-- proof
  prop_1_35_1 R H

end TensorCategories


-- created on 2026-10-23
