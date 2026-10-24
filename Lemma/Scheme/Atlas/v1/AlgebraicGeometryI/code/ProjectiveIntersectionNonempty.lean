import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ProjectiveIntersectionNonempty
open Ideal


/--
[withbot_enat_le_of_nat_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma withbot_enat_le_of_nat_bound
  {a d : ℕ}
  {c : WithBot ℕ∞}
-- given
  (h : (a : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) + c)
  (hgt : d + 1 < a) :
-- imply
  (2 : WithBot ℕ∞) ≤ c := by
-- proof
  by_contra hlt
  push Not at hlt
  have hle : c ≤ 1 := Order.le_of_lt_succ hlt
  have ha : a ≤ d + 1 := by
    exact_mod_cast le_trans h (show (↑d : WithBot ℕ∞) + c ≤ ↑d + 1 by gcongr)
  omega

/--
[withbot_enat_codim_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma withbot_enat_codim_bound
  {dimX dimY n : ℕ}
  {c : WithBot ℕ∞}
-- given
  (h : ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) + c)
  (hdim_le : n ≤ dimX + dimY) :
-- imply
  ((dimX + dimY - n + 1 : ℕ) : WithBot ℕ∞) ≤ c := by
-- proof
  by_contra hlt
  push Not at hlt
  have cast_eq : ((dimX + dimY - n + 1 : ℕ) : WithBot ℕ∞) =
    ((dimX + dimY - n : ℕ) : WithBot ℕ∞) + 1 := by push_cast; ring
  rw [cast_eq] at hlt
  have hle : c ≤ ((dimX + dimY - n : ℕ) : WithBot ℕ∞) :=
    ENat.WithBot.lt_add_one_iff.mp hlt
  have bound : ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) ≤
    ((n + 1 : ℕ) : WithBot ℕ∞) + ((dimX + dimY - n : ℕ) : WithBot ℕ∞) :=
    le_trans h (by gcongr)
  have : dimX + 1 + (dimY + 1) ≤ n + 1 + (dimX + dimY - n) := by exact_mod_cast bound
  omega

/--
[ringKrullDim_mvPolynomial_fin_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma ringKrullDim_mvPolynomial_fin_succ
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  ringKrullDim (MvPolynomial (Fin (n + 1)) k) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
-- proof
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_fin,
    ringKrullDim_eq_zero_of_field]
  simp

/--
[ne_top_of_ringKrullDim_quotient_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma ne_top_of_ringKrullDim_quotient_ge_two
  [CommRing R]
  {I : Ideal R}
-- given
  (h : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I)) :
-- imply
  I ≠ ⊤ := by
-- proof
  intro htop
  subst htop
  haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have hbot : ringKrullDim (R ⧸ (⊤ : Ideal R)) = ⊥ := ringKrullDim_eq_bot_of_subsingleton
  rw [hbot] at h
  exact absurd h (not_le.mpr (WithBot.bot_lt_coe _))

/--
[projective_codim_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma projective_codim_bound
  [CommRing R]
  [IsLocalRing R]
  [HasSerreDimensionInequality R]
  {𝔭 𝔮 : Ideal R}
  [𝔭.IsPrime]
  [𝔮.IsPrime] :
-- imply
  ringKrullDim (R ⧸ 𝔭) + ringKrullDim (R ⧸ 𝔮) ≤ ringKrullDim R + ringKrullDim (R ⧸ (𝔭 ⊔ 𝔮)) :=
-- proof
  HasSerreDimensionInequality.dim_ineq

/--
[projective_intersection_nonempty_of_dim_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma projective_intersection_nonempty_of_dim_condition
  [Field k]
  {n dimX dimY : ℕ}
  {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
  [𝔭.IsPrime]
  [𝔮.IsPrime]
-- given
  (_hp_le : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (_hq_le : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (hconeX : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) = ((dimX + 1 : ℕ) : WithBot ℕ∞))
  (hconeY : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) = ((dimY + 1 : ℕ) : WithBot ℕ∞))
  (hserre : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) + ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) ≤ ringKrullDim (MvPolynomial (Fin (n + 1)) k) + ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)))
  (hdim : n < dimX + dimY) :
-- imply
  (2 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)) := by
-- proof
  rw [hconeX, hconeY, ringKrullDim_mvPolynomial_fin_succ] at hserre
  have hserre' : ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) ≤
    ((n + 1 : ℕ) : WithBot ℕ∞) +
    ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)) := by
    have : ((dimX + 1 : ℕ) : WithBot ℕ∞) + ((dimY + 1 : ℕ) : WithBot ℕ∞) =
      ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) := by push_cast; ring
    rwa [this] at hserre
  exact withbot_enat_le_of_nat_bound hserre' (by omega)

/--
[projective_intersection_sup_ne_top_of_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma projective_intersection_sup_ne_top_of_dim
  [Field k]
  {n dimX dimY : ℕ}
  {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
  [𝔭.IsPrime]
  [𝔮.IsPrime]
-- given
  (hp_le : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (hq_le : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (hconeX : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) = ((dimX + 1 : ℕ) : WithBot ℕ∞))
  (hconeY : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) = ((dimY + 1 : ℕ) : WithBot ℕ∞))
  (hserre : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) + ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) ≤ ringKrullDim (MvPolynomial (Fin (n + 1)) k) + ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)))
  (hdim : n < dimX + dimY) :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ :=
-- proof
  ne_top_of_ringKrullDim_quotient_ge_two
    (projective_intersection_nonempty_of_dim_condition n dimX dimY hp_le hq_le
      hconeX hconeY hserre hdim)

/--
[cone_intersection_contains_origin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma cone_intersection_contains_origin
  [Field k]
  {𝔭 𝔮 : Ideal (MvPolynomial σ k)}
-- given
  (hp : 𝔭 ≤ MvPolynomial.variablesIdeal k σ)
  (hq : 𝔮 ≤ MvPolynomial.variablesIdeal k σ) :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ :=
-- proof
  MvPolynomial.sup_ne_top_of_le_variablesIdeal hp hq

/--
[goal76_projective_codim_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma goal76_projective_codim_bound
  [Field k]
  {n dimX dimY : ℕ}
  {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
  [𝔭.IsPrime]
  [𝔮.IsPrime]
-- given
  (_hp_le : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (_hq_le : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (hconeX : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) = ((dimX + 1 : ℕ) : WithBot ℕ∞))
  (hconeY : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) = ((dimY + 1 : ℕ) : WithBot ℕ∞))
  (hserre : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) + ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) ≤ ringKrullDim (MvPolynomial (Fin (n + 1)) k) + ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)))
  (hdim : n ≤ dimX + dimY) :
-- imply
  ((dimX + dimY - n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)) := by
-- proof
  rw [hconeX, hconeY, ringKrullDim_mvPolynomial_fin_succ] at hserre
  have hserre' : ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) ≤
    ((n + 1 : ℕ) : WithBot ℕ∞) +
    ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)) := by
    have : ((dimX + 1 : ℕ) : WithBot ℕ∞) + ((dimY + 1 : ℕ) : WithBot ℕ∞) =
      ((dimX + 1 + (dimY + 1) : ℕ) : WithBot ℕ∞) := by push_cast; ring
    rwa [this] at hserre
  exact withbot_enat_codim_bound hserre' hdim

/--
[goal76_projective_intersection_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersectionNonempty.lean)
-/
@[path]
lemma goal76_projective_intersection_nonempty
  [Field k]
  {n dimX dimY : ℕ}
  {𝔭 𝔮 : Ideal (MvPolynomial (Fin (n + 1)) k)}
  [𝔭.IsPrime]
  [𝔮.IsPrime]
-- given
  (hp_le : 𝔭 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (hq_le : 𝔮 ≤ MvPolynomial.variablesIdeal k (Fin (n + 1)))
  (hconeX : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) = ((dimX + 1 : ℕ) : WithBot ℕ∞))
  (hconeY : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) = ((dimY + 1 : ℕ) : WithBot ℕ∞))
  (hserre : ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔭) + ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ 𝔮) ≤ ringKrullDim (MvPolynomial (Fin (n + 1)) k) + ringKrullDim (MvPolynomial (Fin (n + 1)) k ⧸ (𝔭 ⊔ 𝔮)))
  (hdim : n < dimX + dimY) :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ :=
-- proof
  projective_intersection_sup_ne_top_of_dim n dimX dimY hp_le hq_le
    hconeX hconeY hserre hdim


-- created on 2026-10-23
