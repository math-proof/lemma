import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.PascalCurves
open Polynomial in


/--
[irreducible_dvd_or_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma irreducible_dvd_or_coprime
  [CommRing R]
  [IsBezout R]
  {Q : R}
  {P : R}
-- given
  (hQ : Irreducible Q) :
-- imply
  Q ∣ P ∨ IsCoprime Q P :=
-- proof
  (hQ.isCoprime_or_dvd P).symm.imp_left id

/--
[irreducible_dvd_of_not_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma irreducible_dvd_of_not_coprime
  [CommRing R]
  [IsBezout R]
  {Q P : R}
-- given
  (hQ : Irreducible Q)
  (h : ¬IsCoprime Q P) :
-- imply
  Q ∣ P :=
-- proof
  hQ.dvd_iff_not_isCoprime.mpr h

/--
[irreducible_dvd_iff_not_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma irreducible_dvd_iff_not_coprime
  [CommRing R]
  [IsBezout R]
  {Q P : R}
-- given
  (hQ : Irreducible Q) :
-- imply
  Q ∣ P ↔ ¬IsCoprime Q P :=
-- proof
  hQ.dvd_iff_not_isCoprime

/--
[irreducible_dvd_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma irreducible_dvd_mul
  [CommRing R]
  [IsBezout R]
  {Q a b : R}
-- given
  (hQ : Irreducible Q)
  (h : Q ∣ a * b) :
-- imply
  Q ∣ a ∨ Q ∣ b := by
-- proof
  by_contra hc
  push Not at hc
  have hca : IsCoprime Q a := hQ.coprime_iff_not_dvd.mpr hc.1
  exact hc.2 (hca.dvd_of_dvd_mul_left h)

/--
[natDegree_mul_three_linear_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma natDegree_mul_three_linear_le
  [CommRing R]
  {L₁ L₃ L₅ : Polynomial R}
-- given
  (h₁ : L₁.natDegree ≤ 1)
  (h₃ : L₃.natDegree ≤ 1)
  (h₅ : L₅.natDegree ≤ 1) :
-- imply
  (L₁ * L₃ * L₅).natDegree ≤ 3 :=
-- proof
  calc (L₁ * L₃ * L₅).natDegree
    ≤ (L₁ * L₃).natDegree + L₅.natDegree := Polynomial.natDegree_mul_le
    _ ≤ (L₁.natDegree + L₃.natDegree) + L₅.natDegree :=
      Nat.add_le_add_right Polynomial.natDegree_mul_le _
    _ ≤ 3 := by omega

/--
[pascal_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma pascal_theorem
  [Field k]
  {Q : Polynomial k}
  {F G : Polynomial k}
-- given
  (hQ : Irreducible Q)
  (_hd : Q.natDegree = 2)
  (_hF : F.natDegree ≤ 3)
  (_hG : G.natDegree ≤ 3)
  (h_not_coprime : ¬ IsCoprime Q (F - G)) :
-- imply
  Q ∣ (F - G) :=
-- proof
  (irreducible_dvd_or_coprime hQ (F - G)).resolve_right h_not_coprime

/--
[pascal_collinearity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma pascal_collinearity
  [Field k]
  {Q F G : Polynomial k}
-- given
  (hQm : Q.Monic)
  (hQd : Q.natDegree = 2)
  (hF : F.natDegree ≤ 3)
  (hG : G.natDegree ≤ 3)
  (_hdvd : Q ∣ (F - G)) :
-- imply
  ((F - G) /ₘ Q).natDegree ≤ 1 := by
-- proof
  rw [Polynomial.natDegree_divByMonic _ hQm, hQd]
  have h1 : (F - G).natDegree ≤ 3 :=
    (Polynomial.natDegree_sub_le F G).trans (max_le hF hG)
  omega

/--
[pascal_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma pascal_full
  [Field k]
  {Q : Polynomial k}
  {L₁ L₂ L₃ L₄ L₅ L₆ : Polynomial k}
-- given
  (hQ : Irreducible Q)
  (hQm : Q.Monic)
  (hQd : Q.natDegree = 2)
  (hL₁ : L₁.natDegree ≤ 1)
  (hL₂ : L₂.natDegree ≤ 1)
  (hL₃ : L₃.natDegree ≤ 1)
  (hL₄ : L₄.natDegree ≤ 1)
  (hL₅ : L₅.natDegree ≤ 1)
  (hL₆ : L₆.natDegree ≤ 1)
  (h_not_coprime : ¬ IsCoprime Q (L₁ * L₃ * L₅ - L₂ * L₄ * L₆)) :
-- imply
  Q ∣ (L₁ * L₃ * L₅ - L₂ * L₄ * L₆) ∧ ((L₁ * L₃ * L₅ - L₂ * L₄ * L₆) /ₘ Q).natDegree ≤ 1 := by
-- proof
  refine ⟨?_, ?_⟩
  · exact (irreducible_dvd_or_coprime hQ _).resolve_right h_not_coprime
  · rw [Polynomial.natDegree_divByMonic _ hQm, hQd]
    have hFG : (L₁ * L₃ * L₅ - L₂ * L₄ * L₆).natDegree ≤ 3 :=
      (Polynomial.natDegree_sub_le _ _).trans
        (max_le (natDegree_mul_three_linear_le hL₁ hL₃ hL₅)
          (natDegree_mul_three_linear_le hL₂ hL₄ hL₆))
    omega

/--
[krullDimLE_one_of_ringKrullDim_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma krullDimLE_one_of_ringKrullDim_eq_one
  [CommRing A]
-- given
  (hdim : ringKrullDim A = 1) :
-- imply
  Ring.KrullDimLE 1 A := by
-- proof
  constructor
  simp only [ringKrullDim] at hdim
  exact hdim ▸ le_refl _

/--
[dim_one_prime_is_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma dim_one_prime_is_maximal
  [CommRing A]
  [IsDomain A]
  {p : Ideal A}
-- given
  (hdim : ringKrullDim A = 1)
  (hp : p.IsPrime)
  (hne : p ≠ ⊥) :
-- imply
  p.IsMaximal :=
-- proof
  Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
    (krullDimLE_one_of_ringKrullDim_eq_one hdim) p hne hp

/--
[dim_one_proper_closed_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
lemma dim_one_proper_closed_finite
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {I : Ideal A}
-- given
  (hdim : ringKrullDim A = 1)
  (hI : I ≠ ⊥)
  (_hI' : I ≠ ⊤) :
-- imply
  Set.Finite {p : Ideal A | p.IsPrime ∧ I ≤ p} := by
-- proof
  have hsub : {p : Ideal A | p.IsPrime ∧ I ≤ p} ⊆ I.minimalPrimes := by
    intro p ⟨hp, hIp⟩
    refine ⟨⟨hp, hIp⟩, fun q ⟨hq, hIq⟩ hqp => ?_⟩
    have hqne : q ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hIq))
    exact (dim_one_prime_is_maximal hdim hq hqne).eq_of_le hp.ne_top hqp |>.ge
  exact (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).subset hsub

/--
[cofinite_continuous_of_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PascalCurves.lean)
-/
@[path]
private lemma cofinite_continuous_of_equiv_eq
  {X Y : Type*}
  {e : X ≃ Y} :
-- imply
  Continuous (cofiniteEquiv X Y e) := by
-- proof
  apply cofinite_continuous_of_equiv X Y e


-- created on 2026-10-23
