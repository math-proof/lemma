/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/IrreducibleCharacterBasis.lean -/


import Def.GroupTheory.IrreducibleCharacterBasis.Part2
import Lemma.Representation.Simple_Of
import Mathlib.Analysis.Complex.Polynomial.Basic
open CategoryTheory
open MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted


noncomputable section

-- Equal pairings against all irreducible characters determine a class function.
example {G : Type*} [Group G] [Finite G] (f₁ f₂ : G → ℂ)
    (hf₁ : ∀ g h : G, f₁ (h * g * h⁻¹) = f₁ g)
    (hf₂ : ∀ g h : G, f₂ (h * g * h⁻¹) = f₂ g)
    (hpair : ∀ (W : FDRep ℂ G) [Simple W],
      (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, f₁ g * W.character g⁻¹ =
        (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G, f₂ g * W.character g⁻¹) :
    f₁ = f₂ := by
  apply sub_eq_zero.mp
  apply FDRep.eq_zero_of_isClassFunction_of_orthogonal (f₁ - f₂)
  · intro g h
    simp only [Pi.sub_apply]
    rw [hf₁ g h, hf₂ g h]
  · intro W hW
    let _ := Fintype.ofFinite G
    simp only [Pi.sub_apply, sub_mul, finsum_eq_sum_of_fintype,
      Finset.sum_sub_distrib, mul_sub]
    exact sub_eq_zero.mpr (by simpa only [finsum_eq_sum_of_fintype] using hpair W)

-- A vanishing combination of two nonisomorphic simple characters has zero coefficients.
example {G : Type*} [Group G] [Finite G] (V W : FDRep ℂ G)
    [Simple V] [Simple W] (hVW : ¬Nonempty (V ≅ W)) (a b : ℂ)
    (h : a • V.character + b • W.character = 0) : a = 0 ∧ b = 0 := by
  let _ : ∀ i, Simple (![V, W] i) := by
    intro i
    fin_cases i
    · simpa using (inferInstance : Simple V)
    · simpa using (inferInstance : Simple W)
  have hLI' := FDRep.linearIndependent_character ![V, W] (by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hVW (by simpa using hij)).elim
    · exact (hVW ⟨by simpa using hij.some.symm⟩).elim
    · rfl)
  have hLI : LinearIndependent ℂ ![V.character, W.character] := by
    convert hLI' using 1
    ext i g
    fin_cases i <;> rfl
  exact (LinearIndependent.pair_iff.mp hLI) a b h

-- An irreducible representation yields an irreducible character of norm one.
example {G : Type*} {V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    (FDRep.of ρ).character ∈
        {χ : G → ℂ | ∃ W : FDRep ℂ G, Simple W ∧ W.character = χ} ∧
      (Nat.card G : ℂ)⁻¹ * ∑ᶠ g : G,
        (FDRep.of ρ).character g * (FDRep.of ρ).character g⁻¹ = 1 := by
  let _ := Fintype.ofFinite G
  let _ : NeZero (Nat.card G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)⟩
  let _ : Simple (FDRep.of ρ) := FDRep.simple_of_isIrreducible ρ
  constructor
  · exact ⟨FDRep.of ρ, inferInstance, rfl⟩
  · have hself := FDRep.char_orthonormal (FDRep.of ρ) (FDRep.of ρ)
    rw [ite_eq_left ⟨Iso.refl (FDRep.of ρ)⟩] at hself
    simpa only [finsum_eq_sum_of_fintype] using hself

section

attribute [local instance] Classical.propDecidable

-- The identity indicator is a class function and hence an irreducible-character sum.
example (G : Type*) [Group G] [Finite G] :
    (fun g : G ↦ if g = 1 then (1 : ℂ) else 0) ∈ Submodule.span ℂ
      {χ : G → ℂ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} := by
  apply mem_span_irrCharacters_of_isClassFunction G
  intro g h
  by_cases hg : g = 1
  · subst g
    simp
  · have hconj : h * g * h⁻¹ ≠ 1 := by
      intro heq
      apply hg
      calc
        g = h⁻¹ * (h * g * h⁻¹) * h := by group
        _ = h⁻¹ * 1 * h := by rw [heq]
        _ = 1 := by group
    rw [ite_eq_right hconj, ite_eq_right hg]

end

-- A finite commutative group has one irreducible character per group element.
example (G : Type*) [CommGroup G] [Finite G] :
    Nat.card {χ : G → ℂ // ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ} =
      Nat.card G := by
  rw [card_irrCharacters_eq_card_conjClasses]
  exact (Nat.card_congr ConjClasses.mkEquiv).symm

end
