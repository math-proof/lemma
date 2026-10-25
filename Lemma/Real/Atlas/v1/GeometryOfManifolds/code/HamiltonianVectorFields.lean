import Mathlib
import sympy.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
open DifferentialFormSpace


/--
[ι_squared_zero_on_2forms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
$\iota_X \iota_X \alpha = 0$. -/
lemma ι_squared_zero_on_2forms
  {Ω : ℕ → Type*} {VF : Type*}
  [inst : DifferentialFormSpace Ω VF]
  (X : VF) (α : Ω 2) :
  inst.ι X (inst.ι X α) = (0 : Ω 0) :=
  inst.ι_squared X α

/--
[ι_ι_skew_2form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
$\iota_Y \iota_X \alpha = -\iota_X \iota_Y \alpha$. -/
lemma ι_ι_skew_2form
  {Ω : ℕ → Type*} {VF : Type*}
  [inst : DifferentialFormSpace Ω VF]
  (X Y : VF) (α : Ω 2) :
  inst.ι Y (inst.ι X α) = -(inst.ι X (inst.ι Y α)) :=
  inst.ι_ι_anticomm Y X α

/--
[HamiltonianFlow.preserves_lie_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma HamiltonianFlow.preserves_lie_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {H : Ω 0}
  {hv : HamiltonianVectorField S H}
  {flow : HamiltonianFlow S H hv}
  {t : ℝ}
  {p : ℕ}
  {α : Ω p}
-- given
  (hL : inst.L hv.X α = 0) :
-- imply
  (flow.ρ_t t).pullback α = α := by
-- proof
  apply flow.deriv_zero_const α _ t
  intro s
  rw [flow.flow_ode s α, hL]
  have := (flow.ρ_t s).pullback_smul (0 : ℝ) (0 : Ω p)
  simp only [zero_smul] at this
  exact this

/--
[HamiltonianFlow.preserves_symplectic_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma HamiltonianFlow.preserves_symplectic_form
  {Ω : ℕ → Type*}
  [DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {H : Ω 0}
  {hv : HamiltonianVectorField S H}
  {flow : HamiltonianFlow S H hv}
  {t : ℝ} :
-- imply
  (flow.ρ_t t).pullback S.ω = S.ω :=
-- proof
  flow.preserves_lie_zero t S.ω (lie_deriv_hamiltonian_eq_zero S H hv)

/--
[hamiltonian_flow_preserves_symplectic_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma hamiltonian_flow_preserves_symplectic_form
  {Ω : ℕ → Type*}
  [DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {H : Ω 0}
  {flow : HamiltonianFlow S H hv}
  {t : ℝ}
-- given
  (hv : HamiltonianVectorField S H) :
-- imply
  (flow.ρ_t t).pullback S.ω = S.ω :=
-- proof
  flow.preserves_symplectic_form t

/--
[isSymplecticVF_iff_ιXω_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
$\iota_X \omega$ is a closed 1-form. This follows from Cartan's formula together with
$d\omega = 0$. -/
lemma isSymplecticVF_iff_ιXω_closed
  {Ω : ℕ → Type*} {VF : Type*}
  [inst : DifferentialFormSpace Ω VF]
  (S : SymplecticManifold Ω VF)
  (X : VF) :
  IsSymplecticVectorField S X ↔ IsClosed' VF (inst.ι X S.ω) := by
  unfold IsSymplecticVectorField IsClosed'
  constructor
  ·
    intro h
    have hcartan := cartan_formula X S.ω
    rw [S.closed, ι_zero_val, add_zero] at hcartan
    rw [← hcartan]; exact h
  ·
    intro h
    rwa [cartan_formula X S.ω, S.closed, ι_zero_val, add_zero]

/--
[hamiltonianVF_isHamiltonianVF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma hamiltonianVF_isHamiltonianVF
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {H : Ω 0}
-- given
  (hv : HamiltonianVectorField S H) :
-- imply
  IsHamiltonianVectorField S hv.X :=
-- proof
  ⟨H, hv.defining_eq⟩

/--
[poissonBracket_eq_neg_lie_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma poissonBracket_eq_neg_lie_deriv
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {F G : Ω 0}
-- given
  (hvF : HamiltonianVectorField S F)
  (hvG : HamiltonianVectorField S G) :
-- imply
  poissonBracket S hvF hvG = -(inst.L hvF.X G) := by
-- proof
  show inst.ι hvG.X (inst.ι hvF.X S.ω) = -(inst.L hvF.X G)
  rw [ι_ι_skew_2form hvF.X hvG.X S.ω, hvG.defining_eq]
  rw [inst.L_zero_eq_ι_d hvF.X G]

/--
[lie_bracket_ι_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
$\iota_{[X, Y]} \alpha = \mathcal{L}_X (\iota_Y \alpha) - \iota_Y (\mathcal{L}_X \alpha)$. -/
lemma lie_bracket_ι_eq
  {Ω : ℕ → Type*} {VF : Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  (X Y : VF) {p : ℕ} (α : Ω (p + 1)) :
  inst.ι (hbr.bracket X Y) α = inst.L X (inst.ι Y α) - inst.ι Y (inst.L X α) :=
  hbr.bracket_ι_eq X Y α

/--
[L_bracket_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma L_bracket_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  {X Y : VF}
  {p : ℕ}
  {α : Ω p} :
-- imply
  inst.L (hbr.bracket X Y) α = inst.L X (inst.L Y α) - inst.L Y (inst.L X α) := by
-- proof
  induction p with
  | zero =>
    rw [inst.L_zero_eq_ι_d (hbr.bracket X Y) α]
    rw [lie_bracket_ι_eq X Y (inst.d α)]
    rw [← inst.L_zero_eq_ι_d Y α]
    rw [inst.L_comm_d X α]
    rw [← inst.L_zero_eq_ι_d Y (inst.L X α)]
  | succ n ih =>
    have L_neg : ∀ (Z : VF) {q : ℕ} (β : Ω q), inst.L Z (-β) = -(inst.L Z β) := by
      intro Z q β
      have h := inst.L_smul Z (-1 : ℝ) β
      simp at h; exact h
    have L_sub : ∀ (Z : VF) {q : ℕ} (a b : Ω q),
      inst.L Z (a - b) = inst.L Z a - inst.L Z b := by
      intro Z q a b
      rw [sub_eq_add_neg, inst.L_add, L_neg, ← sub_eq_add_neg]
    have fMul_sub_left : ∀ {q : ℕ} (a b : Ω 0) (c : Ω q),
      inst.fMul (a - b) c = inst.fMul a c - inst.fMul b c := by
      intro q a b c
      rw [sub_eq_add_neg, inst.fMul_add_left, sub_eq_add_neg]
      congr 1
      have h := inst.fMul_smul (-1 : ℝ) b c
      simp at h; exact h
    have d_sub : ∀ {q : ℕ} (a b : Ω q),
      inst.d (a - b) = inst.d a - inst.d b := by
      intro q a b
      rw [sub_eq_add_neg, inst.d_add, sub_eq_add_neg]
      congr 1
      have h := inst.d_smul (-1 : ℝ) b
      simp at h; exact h
    have fMul_sub_right : ∀ {q : ℕ} (g : Ω 0) (a b : Ω q),
      inst.fMul g (a - b) = inst.fMul g a - inst.fMul g b := by
      intro q g a b
      rw [sub_eq_add_neg, inst.fMul_add_right, sub_eq_add_neg]
      congr 1
      have h1 : inst.fMul g (b + (-b)) = inst.fMul g b + inst.fMul g (-b) :=
        inst.fMul_add_right g b (-b)
      rw [add_neg_cancel, DifferentialFormSpace.fMul_zero] at h1
      exact eq_neg_of_add_eq_zero_right h1.symm
    have key : inst.L (hbr.bracket X Y) α - inst.L X (inst.L Y α) +
      inst.L Y (inst.L X α) = 0 := by
      apply inst.ext_fdα
        (fun β => inst.L (hbr.bracket X Y) β - inst.L X (inst.L Y β) +
          inst.L Y (inst.L X β))
      ·
        intro a b
        simp only [inst.L_add]
        abel
      ·
        intro r a
        simp only [inst.L_smul]
        simp [smul_sub, smul_add]
      ·
        intro f γ
        have ih_f : inst.L (hbr.bracket X Y) f =
          inst.L X (inst.L Y f) - inst.L Y (inst.L X f) := by
          rw [inst.L_zero_eq_ι_d (hbr.bracket X Y) f]
          rw [lie_bracket_ι_eq X Y (inst.d f)]
          rw [← inst.L_zero_eq_ι_d Y f]
          rw [inst.L_comm_d X f]
          rw [← inst.L_zero_eq_ι_d Y (inst.L X f)]
        have ih_γ : inst.L (hbr.bracket X Y) γ =
          inst.L X (inst.L Y γ) - inst.L Y (inst.L X γ) := ih γ
        have e1 : inst.L (hbr.bracket X Y) (inst.fMul f (inst.d γ)) =
          inst.fMul (inst.L (hbr.bracket X Y) f) (inst.d γ) +
          inst.fMul f (inst.d (inst.L (hbr.bracket X Y) γ)) := by
          rw [inst.L_fMul, inst.L_comm_d]
        have e2 : inst.L X (inst.L Y (inst.fMul f (inst.d γ))) =
          inst.L X (inst.fMul (inst.L Y f) (inst.d γ) +
            inst.fMul f (inst.d (inst.L Y γ))) := by
          rw [inst.L_fMul Y, inst.L_comm_d Y]
        have e3 : inst.L Y (inst.L X (inst.fMul f (inst.d γ))) =
          inst.L Y (inst.fMul (inst.L X f) (inst.d γ) +
            inst.fMul f (inst.d (inst.L X γ))) := by
          rw [inst.L_fMul X, inst.L_comm_d X]
        rw [e1, e2, e3]
        rw [inst.L_add X (inst.fMul (inst.L Y f) (inst.d γ))
          (inst.fMul f (inst.d (inst.L Y γ)))]
        rw [inst.L_add Y (inst.fMul (inst.L X f) (inst.d γ))
          (inst.fMul f (inst.d (inst.L X γ)))]
        rw [inst.L_fMul X (inst.L Y f) (inst.d γ)]
        rw [inst.L_fMul X f (inst.d (inst.L Y γ))]
        rw [inst.L_fMul Y (inst.L X f) (inst.d γ)]
        rw [inst.L_fMul Y f (inst.d (inst.L X γ))]
        rw [inst.L_comm_d X γ, inst.L_comm_d Y γ]
        rw [inst.L_comm_d X (inst.L Y γ), inst.L_comm_d Y (inst.L X γ)]
        rw [ih_f, ih_γ]
        rw [fMul_sub_left, d_sub, fMul_sub_right]
        abel
    have goal : inst.L (hbr.bracket X Y) α =
      inst.L (hbr.bracket X Y) α - inst.L X (inst.L Y α) +
      inst.L Y (inst.L X α) +
      (inst.L X (inst.L Y α) - inst.L Y (inst.L X α)) := by abel
    rwa [key, zero_add] at goal

/--
[ι_one_form_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
then $\alpha = 0$. -/
lemma ι_one_form_nondegenerate
  {Ω : ℕ → Type*} {VF : Type*}
  [inst : DifferentialFormSpace Ω VF]
  (α : Ω 1) (h : ∀ (X : VF), inst.ι X α = (0 : Ω 0)) :
  α = 0 :=
  inst.ι_one_form_nondegenerate α h

/--
[lie_bracket_hamiltonian_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma lie_bracket_hamiltonian_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  {F G : Ω 0}
-- given
  (hvF : HamiltonianVectorField S F)
  (hvG : HamiltonianVectorField S G) :
-- imply
  inst.ι (hbr.bracket hvF.X hvG.X) S.ω = inst.d (inst.L hvF.X G) := by
-- proof
  rw [lie_bracket_ι_eq hvF.X hvG.X S.ω]
  rw [hvG.defining_eq]
  rw [lie_deriv_hamiltonian_eq_zero S F hvF]
  rw [inst.L_comm_d hvF.X G]
  rw [ι_zero_val, sub_zero]

/--
[TimeDependentHamiltonianFlow.preserves_lie_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma TimeDependentHamiltonianFlow.preserves_lie_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {flow : TimeDependentHamiltonianFlow S}
  {t : ℝ}
  {p : ℕ}
  {α : Ω p}
-- given
  (hL : ∀ s, inst.L (flow.hv_t s).X α = 0) :
-- imply
  (flow.φ_t t).pullback α = α := by
-- proof
  apply flow.deriv_zero_const α _ t
  intro s
  rw [flow.flow_ode s α, hL s]
  have := (flow.φ_t s).pullback_smul (0 : ℝ) (0 : Ω p)
  simp only [zero_smul] at this
  exact this

/--
[TimeDependentHamiltonianFlow.preserves_symplectic_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma TimeDependentHamiltonianFlow.preserves_symplectic_form
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {flow : TimeDependentHamiltonianFlow S}
  {t : ℝ} :
-- imply
  (flow.φ_t t).pullback S.ω = S.ω :=
-- proof
  flow.preserves_lie_zero t S.ω
    (fun s => lie_deriv_hamiltonian_eq_zero S (flow.H_t s) (flow.hv_t s))

/--
[SymplecticIsotopy.ofHamiltonian_isHamiltonian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma SymplecticIsotopy.ofHamiltonian_isHamiltonian
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {flow : TimeDependentHamiltonianFlow S} :
-- imply
  (SymplecticIsotopy.ofHamiltonian flow).IsHamiltonian := by
-- proof
  intro t
  exact hamiltonianVF_isHamiltonianVF S (flow.H_t t) (flow.hv_t t)

/--
[exact_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma exact_add
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α β : Ω (p + 1)}
-- given
  (hα : IsExact' VF α)
  (hβ : IsExact' VF β) :
-- imply
  IsExact' VF (α + β) := by
-- proof
  obtain ⟨a, ha⟩ := hα
  obtain ⟨b, hb⟩ := hβ
  exact ⟨a + b, by rw [ha, hb, inst.d_add]⟩

/--
[exact_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma exact_neg
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α : Ω (p + 1)}
-- given
  (hα : IsExact' VF α) :
-- imply
  IsExact' VF (-α) := by
-- proof
  obtain ⟨a, ha⟩ := hα
  exact ⟨-a, by rw [ha, d_neg]⟩

/--
[exact_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
lemma exact_sub
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {p : ℕ}
  {α β : Ω (p + 1)}
-- given
  (hα : IsExact' VF α)
  (hβ : IsExact' VF β) :
-- imply
  IsExact' VF (α - β) := by
-- proof
  rw [sub_eq_add_neg]
  exact exact_add α (-β) hα (exact_neg β hβ)

/--
[lie_deriv_hamiltonian_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
private lemma lie_deriv_hamiltonian_eq_zero_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {H : Ω 0}
-- given
  (hv : HamiltonianVectorField S H) :
-- imply
  inst.L hv.X S.ω = (0 : Ω 2) := by
-- proof
  apply lie_deriv_hamiltonian_eq_zero S H hv

/--
[isSymplecticVF_iff_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
private lemma isSymplecticVF_iff__eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S : SymplecticManifold Ω VF}
  {X : VF} :
-- imply
  IsSymplecticVectorField S X ↔ IsClosed' VF (inst.ι X S.ω) := by
-- proof
  apply isSymplecticVF_iff_ S X

/--
[lie_bracket_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean)
-/
@[path]
private lemma lie_bracket__eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  {X Y : VF}
  {p : ℕ}
  {α : Ω (p + 1)} :
-- imply
  inst.ι (hbr.bracket X Y) α = inst.L X (inst.ι Y α) - inst.ι Y (inst.L X α) := by
-- proof
  apply lie_bracket_ X Y α


-- created on 2026-10-23
