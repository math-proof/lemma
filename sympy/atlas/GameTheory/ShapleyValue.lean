/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ShapleyValue.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ext

/-! # Shapley value characterization for cooperative games

Existence and uniqueness of the linear value satisfying efficiency, symmetry,
and the null-player axiom, via unanimity games and Möbius inversion on the
Boolean lattice.

Source: L. S. Shapley, "A Value for n-Person Games," Contributions to the
Theory of Games II, Annals of Mathematics Studies 28, Princeton University
Press (1953), 307--317; modern DOI `10.1515/9781400881970-018`.

Source-fidelity note: Shapley's printed argument (pp. 308--312) works with
superadditive games on a player universe with finite carriers, with axioms of
full permutation equivariance, efficiency for every carrier, and aggregation.
What is proved here is an adapted fixed-finite-player vector-space
characterization: it quantifies over arbitrary normalized set functions on one
fixed finite player type, packages aggregation together with real homogeneity
as linearity, and uses invariant-game symmetry (equal payoffs when a
permutation fixes the game), grand-coalition efficiency, and a null-player
axiom. This characterization is mathematically coherent as stated, but it is
this adapted formulation rather than a literal transcription of the source
theorem.
-/

namespace MathlibExt.GameTheory.ShapleyValue

/-- A cooperative TU-game: real-valued characteristic function normalized at `∅`. -/
@[ext]
structure CoopGame (Player : Type*) where
  charFun : Set Player → ℝ
  empty : charFun ∅ = 0

namespace CoopGame

variable {Player : Type*}

instance : AddCommGroup (CoopGame Player) where
  add v w :=
    ⟨fun S => v.charFun S + w.charFun S, by simp [v.empty, w.empty]⟩
  add_assoc a b c := by
    ext S
    exact add_assoc (a.charFun S) (b.charFun S) (c.charFun S)
  zero := ⟨fun _ => 0, rfl⟩
  zero_add a := by
    ext S
    exact zero_add (a.charFun S)
  add_zero a := by
    ext S
    exact add_zero (a.charFun S)
  nsmul n v :=
    ⟨fun S => n • v.charFun S, by simp [v.empty]⟩
  neg v :=
    ⟨fun S => -v.charFun S, by simp [v.empty]⟩
  zsmul n v :=
    ⟨fun S => n • v.charFun S, by simp [v.empty]⟩
  neg_add_cancel a := by
    ext S
    exact neg_add_cancel (a.charFun S)
  add_comm a b := by
    ext S
    exact add_comm (a.charFun S) (b.charFun S)

instance : SMul ℝ (CoopGame Player) where
  smul c v := ⟨fun S => c * v.charFun S, by simp [v.empty]⟩

instance : Module ℝ (CoopGame Player) where
  one_smul v := by
    ext S
    exact one_mul (v.charFun S)
  mul_smul c₁ c₂ v := by
    ext S
    exact mul_assoc c₁ c₂ (v.charFun S)
  smul_zero c := by
    ext S
    exact mul_zero c
  smul_add c v w := by
    ext S
    exact mul_add c (v.charFun S) (w.charFun S)
  add_smul c₁ c₂ v := by
    ext S
    exact add_mul c₁ c₂ (v.charFun S)
  zero_smul v := by
    ext S
    exact zero_mul (v.charFun S)

end CoopGame

variable {Player : Type*} [DecidableEq Player] [Fintype Player]

/-- `i` is null/dummy in `v` if it never changes worth of a coalition not containing it. -/
def IsNullPlayer (v : CoopGame Player) (i : Player) : Prop :=
  ∀ S : Set Player, i ∉ S → v.charFun (insert i S) = v.charFun S

/-- Efficiency: total allocated equals worth of grand coalition. -/
def IsEfficient (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ v : CoopGame Player, ∑ i : Player, φ v i = v.charFun Set.univ

/-- Symmetry under permutations preserving the game via `σ '' S`. -/
def IsSymmetric (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ (σ : Equiv.Perm Player) (v : CoopGame Player),
    (∀ S : Set Player, v.charFun (σ '' S) = v.charFun S) →
    ∀ i : Player, φ v (σ i) = φ v i

/-- Null/dummy player axiom: a null player receives zero. -/
def SatisfiesNullPlayerAxiom (φ : CoopGame Player →ₗ[ℝ] (Player → ℝ)) : Prop :=
  ∀ (v : CoopGame Player) (i : Player), IsNullPlayer v i → φ v i = 0

-- Classical decidability for the subset tests in unanimity-game statements.
attribute [local instance] Classical.propDecidable

/-- Unanimity game: worth 1 iff `T ⊆ S` (zero game when `T = ∅`, since the
constant-1 function is not normalized). -/
private noncomputable def unanimity (T : Finset Player) : CoopGame Player := by
  classical
  exact if h : T = ∅ then 0
  else
    ⟨fun S => if (T : Set Player) ⊆ S then (1 : ℝ) else 0, by
      rw [ite_eq_right]
      intro hsub
      apply h
      exact Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp hsub)⟩

omit [DecidableEq Player] [Fintype Player] in
private theorem charFun_add (v w : CoopGame Player) (S : Set Player) :
    (v + w).charFun S = v.charFun S + w.charFun S :=
  rfl

omit [DecidableEq Player] [Fintype Player] in
private theorem charFun_smul (c : ℝ) (v : CoopGame Player) (S : Set Player) :
    (c • v).charFun S = c * v.charFun S :=
  rfl

omit [DecidableEq Player] [Fintype Player] in
private theorem charFun_sum {ι : Type*} (s : Finset ι)
    (F : ι → CoopGame Player)
    (S : Set Player) :
    (∑ T ∈ s, F T).charFun S = ∑ T ∈ s, (F T).charFun S := by
  classical
  induction s using Finset.induction with
  | empty => simp [charFun_zero]
  | insert _ _ ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, charFun_add, ih]

/-- Möbius coefficient of `v` at `T`. -/
private noncomputable def mobiusCoeff (v : CoopGame Player) (T : Finset Player) : ℝ :=
  ∑ R ∈ T.powerset, (-1 : ℝ) ^ (T.card - R.card) * v.charFun ↑R

/-- Every game is a combination of unanimity games with Möbius coefficients. -/
private theorem game_expansion (v : CoopGame Player) :
    v = ∑ T ∈ Finset.univ.powerset.filter (fun T => T ≠ ∅),
      mobiusCoeff v T • unanimity T := by
  classical
  ext S
  have hF : ∀ T ∈ Finset.univ.powerset.filter (fun T => T ≠ ∅),
      (mobiusCoeff v T • unanimity T).charFun S
      = (if (T : Set Player) ⊆ S then mobiusCoeff v T else 0) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    rw [charFun_smul, unanimity_charFun hT.2]
    by_cases h : (T : Set Player) ⊆ S <;> simp [h]
  rw [charFun_sum, Finset.sum_congr rfl hF, ← Finset.sum_filter]
  have hsub_iff : ∀ T : Finset Player, T ⊆ S.toFinset ↔ (T : Set Player) ⊆ S := by
    intro T
    have hcoe : ((S.toFinset : Finset Player) : Set Player) = S := Set.coe_toFinset S
    have h := Finset.coe_subset (s₁ := T) (s₂ := S.toFinset)
    rw [hcoe] at h
    exact h.symm
  have hset : (Finset.univ.powerset.filter (fun T => T ≠ ∅)).filter
        (fun T : Finset Player => (T : Set Player) ⊆ S)
      = S.toFinset.powerset.filter (fun T => T ≠ ∅) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨-, hne⟩, hsub⟩
      exact ⟨(hsub_iff T).mpr hsub, hne⟩
    · rintro ⟨hsub, hne⟩
      exact ⟨⟨Finset.subset_univ T, hne⟩, (hsub_iff T).mp hsub⟩
  rw [hset]
  have hinv := mobius_inversion v S.toFinset
  rw [Set.coe_toFinset] at hinv
  rw [hinv]
  have hsub0 : S.toFinset.powerset.filter (fun T => T ≠ ∅) ⊆ S.toFinset.powerset :=
    Finset.filter_subset _ _
  have hzero : ∀ T ∈ S.toFinset.powerset,
      T ∉ S.toFinset.powerset.filter (fun T => T ≠ ∅) → mobiusCoeff v T = 0 := by
    intro T hT hnT
    have hTeq : T = ∅ := by
      by_contra hne
      rw [Finset.mem_filter] at hnT
      exact hnT ⟨hT, hne⟩
    subst hTeq
    exact mobiusCoeff_empty v
  exact (Finset.sum_subset hsub0 hzero).symm

omit [DecidableEq Player] in
private theorem shapley_uniqueness (φ₁ φ₂ : CoopGame Player →ₗ[ℝ] (Player → ℝ))
    (h1e : IsEfficient φ₁) (h1s : IsSymmetric φ₁)
    (h1n : SatisfiesNullPlayerAxiom φ₁)
    (h2e : IsEfficient φ₂) (h2s : IsSymmetric φ₂)
    (h2n : SatisfiesNullPlayerAxiom φ₂) :
    φ₁ = φ₂ := by
  apply LinearMap.ext
  intro v
  rw [game_expansion v, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [map_smul, map_smul]
  have hagree := agree_on_unanimity φ₁ φ₂ h1e h1s h1n h2e h2s h2n T
  rw [hagree]

omit [DecidableEq Player] [Fintype Player] in
private theorem mobiusCoeff_add (v w : CoopGame Player) (T : Finset Player) :
    mobiusCoeff (v + w) T = mobiusCoeff v T + mobiusCoeff w T := by
  unfold mobiusCoeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _
  rw [charFun_add, mul_add]

omit [DecidableEq Player] [Fintype Player] in
private theorem mobiusCoeff_smul (c : ℝ) (v : CoopGame Player) (T : Finset Player) :
    mobiusCoeff (c • v) T = c * mobiusCoeff v T := by
  unfold mobiusCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  rw [charFun_smul]
  ring

private noncomputable def shapleyLM : CoopGame Player →ₗ[ℝ] (Player → ℝ) where
  toFun v := fun i =>
    ∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
      mobiusCoeff v T / (T.card : ℝ)
  map_add' v w := by
    funext i
    change (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff (v + w) T / (T.card : ℝ))
        = (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff v T / (T.card : ℝ))
        + (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff w T / (T.card : ℝ))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    rw [mobiusCoeff_add, add_div]
  map_smul' c v := by
    funext i
    change (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff (c • v) T / (T.card : ℝ))
        = c • (∑ T ∈ Finset.univ.powerset.filter (fun T => i ∈ T),
            mobiusCoeff v T / (T.card : ℝ))
    rw [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [mobiusCoeff_smul, mul_div_assoc]

omit [DecidableEq Player] in
theorem shapley_characterization : ∃! φ : CoopGame Player →ₗ[ℝ] (Player → ℝ),
    IsEfficient φ ∧ IsSymmetric φ ∧ SatisfiesNullPlayerAxiom φ := by
  refine ExistsUnique.intro shapleyLM
    ⟨shapley_efficient, shapley_symmetric, shapley_null⟩ ?_
  intro φ hφ
  obtain ⟨he, hs, hn⟩ := hφ
  exact shapley_uniqueness φ shapleyLM he hs hn
    shapley_efficient shapley_symmetric shapley_null

end MathlibExt.GameTheory.ShapleyValue
