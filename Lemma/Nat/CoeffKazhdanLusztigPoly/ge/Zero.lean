import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.LieGroups.code.Goal139_KLProperties


/--
[kl_positivity_for_grothendieck_group](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Goal139_KLProperties.lean)
-/
@[path]
private lemma kl_positivity_for_grothendieck_group
  {R : Type u}
  [Field R]
  [IsAlgClosed R]
  [CharZero R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {C : CoxeterGroupData}
  {y w : C.W}
  {n : ℕ} :
-- imply
  0 ≤ (KazhdanLusztigPoly C y w).coeff n :=
-- proof
  kazhdan_lusztig_conjecture_nonneg C y w n

/--
[kl_multiplicity_in_grothendieck_group](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Goal139_KLProperties.lean)
-/
@[path]
private lemma kl_multiplicity_in_grothendieck_group
  {R : Type u}
  [Field R]
  [IsAlgClosed R]
  [CharZero R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {C : CoxeterGroupData}
  {compat : CoxeterWeylCompatibility C rd wg}
  {lam : Δ.𝔥 →ₗ[R] R}
  {y w : C.W}
-- given
  (hlam_dr : IsDominantRegularWeight rd wg lam) :
-- imply
  (categoryO_multiplicity C rd wg compat lam y w : ℤ) = (KazhdanLusztigPoly C y w).eval 1 :=
-- proof
  kazhdan_lusztig_conjecture_multiplicity C rd wg compat lam hlam_dr y w


-- created on 2026-10-24
