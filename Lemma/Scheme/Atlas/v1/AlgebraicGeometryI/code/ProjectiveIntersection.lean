import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ProjectiveIntersection
open Ideal MvPolynomial
open MvPolynomial


/--
[ringKrullDim_quotient_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma ringKrullDim_quotient_top
  {R : Type*}
  [CommRing R] :
-- imply
  ringKrullDim (R ⧸ (⊤ : Ideal R)) = ⊥ := by
-- proof
  haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  exact ringKrullDim_eq_bot_of_subsingleton

/--
[sup_ne_top_of_dim_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma sup_ne_top_of_dim_inequality
  [CommRing R]
  {𝔭 𝔮 : Ideal R}
  [𝔭.IsPrime]
  [𝔮.IsPrime]
-- given
  (hdim : ringKrullDim (R ⧸ 𝔭) + ringKrullDim (R ⧸ 𝔮) ≤ ringKrullDim R + ringKrullDim (R ⧸ (𝔭 ⊔ 𝔮))) :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ := by
-- proof
  intro htop
  rw [htop, ringKrullDim_quotient_top, WithBot.add_bot] at hdim
  have h1 : (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭) := by
    haveI : Nontrivial (R ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
    exact ringKrullDim_nonneg_of_nontrivial
  have h2 : (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔮) := by
    haveI : Nontrivial (R ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
    exact ringKrullDim_nonneg_of_nontrivial
  exact absurd (le_trans (le_add_of_nonneg_of_le h1 h2) hdim)
    (not_le.mpr (WithBot.bot_lt_coe 0))

/--
[sup_ne_top_of_serre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma sup_ne_top_of_serre
  [CommRing R]
  [IsLocalRing R]
  [HasSerreDimensionInequality R]
  {𝔭 𝔮 : Ideal R}
  [𝔭.IsPrime]
  [𝔮.IsPrime] :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ :=
-- proof
  sup_ne_top_of_dim_inequality HasSerreDimensionInequality.dim_ineq

/--
[sum_of_primes_proper_of_height_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma sum_of_primes_proper_of_height_bound
  [CommRing R]
  [IsDomain R]
  [IsNoetherianRing R]
  [IsLocalRing R]
  [HasSerreDimensionInequality R]
  {𝔭 𝔮 : Ideal R}
  [𝔭.IsPrime]
  [𝔮.IsPrime]
-- given
  (_h : 𝔭.height + 𝔮.height ≤ ringKrullDim R) :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ :=
-- proof
  sup_ne_top_of_serre

/--
[map_quotient_eq_top_of_sup_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma map_quotient_eq_top_of_sup_eq_top
  [CommRing R]
  {𝔭 𝔮 : Ideal R}
-- given
  (h : 𝔭 ⊔ 𝔮 = ⊤) :
-- imply
  Ideal.map (Ideal.Quotient.mk 𝔭) 𝔮 = ⊤ := by
-- proof
  have : Ideal.map (Ideal.Quotient.mk 𝔭) (𝔭 ⊔ 𝔮) = ⊤ := by
    rw [h]; exact Ideal.map_top _
  rw [Ideal.map_sup, Ideal.map_mk_eq_bot_of_le le_rfl] at this
  simpa using this

/--
[ringKrullDim_quotient_eq_bot_of_sup_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma ringKrullDim_quotient_eq_bot_of_sup_eq_top
  [CommRing R]
  {I J : Ideal R}
-- given
  (h : I ⊔ J = ⊤) :
-- imply
  ringKrullDim (R ⧸ (I ⊔ J)) = ⊥ := by
-- proof
  rw [h]; exact ringKrullDim_quotient_top R

/--
[ringKrullDim_quotient_sup_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma ringKrullDim_quotient_sup_add_le
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
open MvPolynomial

/--
[MvPolynomial.X_mem_variablesIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma MvPolynomial.X_mem_variablesIdeal
  [CommSemiring k]
  {i : σ} :
-- imply
  (MvPolynomial.X i : MvPolynomial σ k) ∈ MvPolynomial.variablesIdeal k σ :=
-- proof
  Ideal.subset_span (Set.mem_range.mpr ⟨i, rfl⟩)

/--
[MvPolynomial.variablesIdeal_le_ker_eval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma MvPolynomial.variablesIdeal_le_ker_eval_zero
  [CommSemiring k] :
-- imply
  MvPolynomial.variablesIdeal k σ ≤ RingHom.ker (MvPolynomial.eval (0 : σ → k)) := by
-- proof
  apply Ideal.span_le.mpr
  intro p hp
  obtain ⟨i, rfl⟩ := hp
  simp [RingHom.mem_ker]

/--
[MvPolynomial.variablesIdeal_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma MvPolynomial.variablesIdeal_ne_top
  {k : Type*}
  [CommSemiring k]
  [Nontrivial k]
  {σ : Type*} :
-- imply
  MvPolynomial.variablesIdeal k σ ≠ ⊤ := by
-- proof
  rw [Ne, Ideal.eq_top_iff_one]
  intro h1
  have := MvPolynomial.variablesIdeal_le_ker_eval_zero h1
  simp [RingHom.mem_ker] at this

/--
[MvPolynomial.span_singleton_X_le_variablesIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma MvPolynomial.span_singleton_X_le_variablesIdeal
  [CommSemiring k]
  {i : σ} :
-- imply
  Ideal.span {(MvPolynomial.X i : MvPolynomial σ k)} ≤ MvPolynomial.variablesIdeal k σ :=
-- proof
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (MvPolynomial.X_mem_variablesIdeal i))

/--
[MvPolynomial.sup_ne_top_of_le_variablesIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma MvPolynomial.sup_ne_top_of_le_variablesIdeal
  [Field k]
  {𝔭 𝔮 : Ideal (MvPolynomial σ k)}
-- given
  (hp : 𝔭 ≤ MvPolynomial.variablesIdeal k σ)
  (hq : 𝔮 ≤ MvPolynomial.variablesIdeal k σ) :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ :=
-- proof
  ne_top_of_le_ne_top (MvPolynomial.variablesIdeal_ne_top k σ) (sup_le hp hq)

/--
[MvPolynomial.iSup_ne_top_of_le_variablesIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma MvPolynomial.iSup_ne_top_of_le_variablesIdeal
  [Field k]
  {𝔭 : ι → Ideal (MvPolynomial σ k)}
-- given
  (h : ∀ i, 𝔭 i ≤ MvPolynomial.variablesIdeal k σ) :
-- imply
  iSup 𝔭 ≠ ⊤ :=
-- proof
  ne_top_of_le_ne_top (MvPolynomial.variablesIdeal_ne_top k σ) (iSup_le h)

/--
[lines_meet_in_P2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma lines_meet_in_P2
  {k : Type*}
  [Field k] :
-- imply
  Ideal.span {(MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) k)} ⊔ Ideal.span {(MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) k)} ≠ ⊤ :=
-- proof
  MvPolynomial.sup_ne_top_of_le_variablesIdeal
    (MvPolynomial.span_singleton_X_le_variablesIdeal 0)
    (MvPolynomial.span_singleton_X_le_variablesIdeal 1)

/--
[line_and_conic_meet_in_P2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma line_and_conic_meet_in_P2
  {k : Type*}
  [Field k] :
-- imply
  Ideal.span {(MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) k)} ⊔ Ideal.span {(MvPolynomial.X (1 : Fin 3) * MvPolynomial.X (1 : Fin 3) - MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) k)} ≠ ⊤ := by
-- proof
  apply MvPolynomial.sup_ne_top_of_le_variablesIdeal
  · exact MvPolynomial.span_singleton_X_le_variablesIdeal 0
  · apply Ideal.span_le.mpr
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    rw [hp]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (MvPolynomial.X_mem_variablesIdeal 1))
      (Ideal.mul_mem_right _ _ (MvPolynomial.X_mem_variablesIdeal 0))

/--
[planes_meet_in_P4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma planes_meet_in_P4
  {k : Type*}
  [Field k] :
-- imply
  (Ideal.span {(MvPolynomial.X (0 : Fin 5) : MvPolynomial (Fin 5) k), MvPolynomial.X (1 : Fin 5)}) ⊔ (Ideal.span {(MvPolynomial.X (2 : Fin 5) : MvPolynomial (Fin 5) k), MvPolynomial.X (3 : Fin 5)}) ≠ ⊤ := by
-- proof
  apply MvPolynomial.sup_ne_top_of_le_variablesIdeal <;>
  apply Ideal.span_le.mpr <;>
  intro p hp <;>
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp <;>
  obtain rfl | rfl <;> := hp
  exact MvPolynomial.X_mem_variablesIdeal _

/--
[Ideal.sup_ne_top_of_le_proper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma Ideal.sup_ne_top_of_le_proper
  [CommRing R]
  {𝔭 𝔮 𝔪 : Ideal R}
-- given
  (hp : 𝔭 ≤ 𝔪)
  (hq : 𝔮 ≤ 𝔪)
  (hm : 𝔪 ≠ ⊤) :
-- imply
  𝔭 ⊔ 𝔮 ≠ ⊤ :=
-- proof
  ne_top_of_le_ne_top hm (sup_le hp hq)

/--
[Ideal.iSup_ne_top_of_le_proper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveIntersection.lean)
-/
@[path]
lemma Ideal.iSup_ne_top_of_le_proper
  [CommRing R]
  {𝔭 : ι → Ideal R}
  {𝔪 : Ideal R}
-- given
  (h : ∀ i, 𝔭 i ≤ 𝔪)
  (hm : 𝔪 ≠ ⊤) :
-- imply
  iSup 𝔭 ≠ ⊤ :=
-- proof
  ne_top_of_le_ne_top hm (iSup_le h)


-- created on 2026-10-23
