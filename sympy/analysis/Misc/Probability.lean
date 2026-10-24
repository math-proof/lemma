import Mathlib
/-! Some finite probability theory -/

namespace ProbabilityTheory

class FinitelyAdditive (A:Type*) [BooleanAlgebra A] where
  prob : A → ℝ
  prob_top : prob ⊤ = 1
  prob_nonneg (E:A) : 0 ≤ prob E
  prob_disj_sup {E F:A} (hEF: Disjoint E F) : prob (E ⊔ F) = prob E + prob F

namespace FinitelyAdditive

instance instFunLike (A:Type*) [BooleanAlgebra A] :
    DFunLike (FinitelyAdditive A) A (fun _ => ℝ) :=
  { coe := fun P => P.prob
    coe_injective := by
      intro f g h
      cases f
      cases g
      congr }

variable {A:Type*} [BooleanAlgebra A] (P: FinitelyAdditive A)
         {A':Type*} [BooleanAlgebra A'] (P': FinitelyAdditive A')

@[simp]
theorem top : P ⊤ = 1 := P.prob_top

theorem nonneg (E:A) : 0 ≤ P E := P.prob_nonneg E

theorem disj_sup {E F:A} (hEF: Disjoint E F) : P (E ⊔ F) = P E + P F := P.prob_disj_sup hEF

@[simp]
theorem bot : P ⊥ = 0 := by
  have : Disjoint (⊥:A) ⊥ := fun ⦃x⦄ a _ ↦ a
  replace := P.disj_sup this
  simpa using this

@[simp]
theorem compl (E:A) : P Eᶜ = 1 - P E := by
  have : Disjoint Eᶜ E := disjoint_compl_left
  replace := P.disj_sup this
  simp at this
  linarith

theorem le_one (E:A) : P E ≤ 1 := by
  linarith [P.compl E, P.nonneg Eᶜ]

theorem ge_eq_add_diff {E F:A} (hEF: E ≤ F) : P F = P (F \ E) + P E := by
  have : Disjoint (F \ E) E := disjoint_sdiff_self_left
  replace := P.disj_sup this
  rwa [sdiff_sup_cancel hEF] at this

theorem mono {E F:A} (hEF: E ≤ F) : P E ≤ P F := by
  linarith [P.nonneg (F \ E), P.ge_eq_add_diff hEF]

theorem sup_add_inf (E F:A) : P (E ⊔ F) + P (E ⊓ F) = P E + P F := by
  have h₁ : E ⊓ F ≤ E := inf_le_left; replace h₁ := P.ge_eq_add_diff h₁
  have h₂ : F ≤ E ⊔ F := le_sup_right; replace h₂ := P.ge_eq_add_diff h₂
  simp at h₁ h₂
  linarith

theorem sup_le_add (E F:A) : P (E ⊔ F) ≤ P E + P F := by
  linarith [P.sup_add_inf E F, P.nonneg (E ⊓ F)]

-- Some API for extending a finitely additive probability space

def _root_.BoundedLatticeHom.preserves (f: BoundedLatticeHom A A') : Prop := ∀ E:A, P' (f E) = P E

@[simp]
theorem _root_.BoundedLatticeHom.preserves.map {f: BoundedLatticeHom A A'} (hf: f.preserves P P') (E:A) : P' (f E) = P E := hf E

-- an example of how a probability space can be extended while preserving various properties

class ExampleProb {A:Type*} [BooleanAlgebra A] (P: FinitelyAdditive A) where
  E : A
  F : A
  G : A
  prob_E : P E = 0.5
  prob_EF : P (E ⊔ F) = 0.75
  prob_EF' : P (E ⊓ F) = 0.25
  prob_EG : P (E \ G) = 0.4
  prob_G : P Gᶜ = 0.3

@[implicit_reducible] def ExampleProb.map {Ω: ExampleProb P} {f: BoundedLatticeHom A A'} (hf: f.preserves P P') : ExampleProb P' where
  E := f Ω.E
  F := f Ω.F
  G := f Ω.G
  prob_E := by simp [hf, Ω.prob_E]
  prob_EF := by simp [hf, Ω.prob_EF, ←map_sup]
  prob_EF' := by simp [hf, Ω.prob_EF', ←map_inf]
  prob_EG := by
    rw [← map_sdiff', hf]
    exact Ω.prob_EG
  prob_G := by
    rw [← map_compl', hf]
    exact Ω.prob_G

end FinitelyAdditive
end ProbabilityTheory
