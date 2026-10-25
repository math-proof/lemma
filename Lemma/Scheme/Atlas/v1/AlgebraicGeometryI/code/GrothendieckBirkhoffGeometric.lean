import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckBirkhoffGeometric.Part2
open BigOperators GBGeometric


namespace GBGeometric

/--
[pid_structure_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean)
-/
@[path]
lemma pid_structure_theorem
  {k : Type*}
  [Field k]
  {M : Type*}
  [AddCommGroup M]
  [Module (Polynomial k) M]
  [Module.Finite (Polynomial k) M]
  [Module.Free (Polynomial k) M] :
-- imply
  ∃ r : ℕ, Nonempty (M ≃ₗ[Polynomial k] (Fin r → Polynomial k)) := by
-- proof
  haveI : Module.IsTorsionFree (Polynomial k) M :=
    (Module.free_iff_isTorsionFree).mp inferInstance
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree'
    (R := Polynomial k) (M := M)
  exact ⟨n, ⟨b.equivFun⟩⟩

end GBGeometric

namespace GBGeometric

/--
[pid_rank_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean)
-/
@[path]
lemma pid_rank_unique
  {k : Type*}
  [Field k]
  {M : Type*}
  [AddCommGroup M]
  [Module (Polynomial k) M]
  [Module.Finite (Polynomial k) M]
  [Module.Free (Polynomial k) M]
  {r s : ℕ}
  {e₁ : M ≃ₗ[Polynomial k] (Fin r → Polynomial k)}
  {e₂ : M ≃ₗ[Polynomial k] (Fin s → Polynomial k)} :
-- imply
  r = s := by
-- proof
  have h₁ : Module.finrank (Polynomial k) (Fin r → Polynomial k) = r :=
    Module.finrank_fin_fun (Polynomial k)
  have h₂ : Module.finrank (Polynomial k) (Fin s → Polynomial k) = s :=
    Module.finrank_fin_fun (Polynomial k)
  have := (e₁.symm.trans e₂).finrank_eq
  rw [h₁, h₂] at this; exact this

end GBGeometric

namespace GBGeometric

/--
[roundtrip_splitting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean)
-/
@[path]
lemma roundtrip_splitting
  [Field k]
  {E : P1VectorBundle k} :
-- imply
  (splittingTypeToBundle k E.hrank_pos E.toSplittingType).splittingType = E.splittingType :=
-- proof
  rfl

end GBGeometric

namespace GBGeometric

/--
[split_bundle_riemann_roch](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean)
-/
@[path]
lemma split_bundle_riemann_roch
  [Field k]
  {E : P1VectorBundle k} :
-- imply
  (E.toSplittingType.h0_twisted 0 : ℤ) - (E.toSplittingType.h1_twisted 0 : ℤ) = (∑ i, E.splittingType i) + E.rank :=
-- proof
GBExistence.split_total_degree E.toSplittingType

end GBGeometric

namespace GBGeometric

/--
[split_bundle_euler_from_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean)
-/
@[path]
lemma split_bundle_euler_from_cech
  {k : Type}
  [Field k]
  {E : P1VectorBundle k} :
-- imply
  ∑ i, GrothendieckBirkhoff.eulerCharP1 k (E.splittingType i) = E.degree + E.rank :=
-- proof
GrothendieckBirkhoff.split_bundle_rr_P1 k E.rank E.splittingType

end GBGeometric

namespace GBGeometric

/--
[line_bundle_euler_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean)
-/
@[path]
lemma line_bundle_euler_cech
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (Module.finrank k (SheafCohomology.H0 k n) : ℤ) - (Module.finrank k (SheafCohomology.H1 k n) : ℤ) = n + 1 :=
-- proof
  SheafCohomology.euler_characteristic k n

end GBGeometric

namespace GBGeometric

/--
[h0_matches_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean)
-/
@[path]
lemma h0_matches_cech
  {k : Type}
  [Field k]
  {d : ℤ} :
-- imply
  (GBExistence.h0_dim d : ℕ) = Module.finrank k (SheafCohomology.H0 k d) := by
-- proof
  by_cases hd : 0 ≤ d
  · exact GBExistence.h0_dim_matches_cohomology k d hd
  · push Not at hd
    exact GBExistence.h0_dim_matches_cohomology_neg k d hd

end GBGeometric

namespace GBGeometric

/--
[h1_matches_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoffGeometric.lean)
-/
@[path]
lemma h1_matches_cech
  {k : Type}
  [Field k]
  {d : ℤ} :
-- imply
  (GBExistence.h1_dim d : ℕ) = Module.finrank k (SheafCohomology.H1 k d) := by
-- proof
  by_cases hd : 0 ≤ d
  · exact GBExistence.h1_dim_matches_cohomology k d hd
  · push Not at hd
    exact GBExistence.h1_dim_matches_cohomology_neg k d hd

end GBGeometric


-- created on 2026-10-23
