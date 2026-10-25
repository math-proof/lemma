import Mathlib
import sympy.Basic
import Structure.v1.Atlas.LieGroups.code.BeilinsonBernstein.Part3
open CategoryTheory BeilinsonBernstein


namespace BeilinsonBernstein

/--
[AlgHom.liftOfSurjectiveNC_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma AlgHom.liftOfSurjectiveNC_apply
  [CommSemiring R]
  [Ring A]
  [Ring B]
  [Ring C]
  [Algebra R A]
  [Algebra R B]
  [Algebra R C]
  {π : A →ₐ[R] B}
  {f : A →ₐ[R] C}
  {x : A}
-- given
  (hπ : Function.Surjective π)
  (hker : ∀ x, π x = 0 → f x = 0) :
-- imply
  AlgHom.liftOfSurjectiveNC π hπ f hker (π x) = f x := by
-- proof
  show f (Function.surjInv hπ (π x)) = f x
  have := hker _ (show π (Function.surjInv hπ (π x) - x) = 0 by
    simp [Function.surjInv_eq])
  rwa [map_sub, sub_eq_zero] at this

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[a₀_factors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.a₀_factors (D : BBDataZero) :
  ∀ (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra),
    D.a₀ (D.proj₀ x) = D.actionMap x :=
  fun x => AlgHom.liftOfSurjectiveNC_apply D.proj₀ D.proj₀_surjective D.actionMap D.ker_inclusion x

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[a₀_filtration_preserving](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.a₀_filtration_preserving (D : BBDataZero) :
  ∀ n (x : D.U₀.carrier), x ∈ D.filtration_U₀ n → D.a₀ x ∈ D.filtration_DF n := by
  intro n x hx
  obtain ⟨u, hu_fil, hu_proj⟩ := D.proj₀_filtration_surj n x hx
  have h_factor : D.a₀ x = D.actionMap u := by
    rw [← hu_proj, D.a₀_factors]
  rw [h_factor]
  exact D.actionMap_filtration_preserving n u hu_fil

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_a₀_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.gr_a₀_compat (D : BBDataZero) :
  ∀ n (x : D.U₀.carrier) (hx : x ∈ D.filtration_U₀ n),
    D.gr_a₀ (D.quotient_U₀ n ⟨x, hx⟩) =
      D.quotient_DF n ⟨D.a₀ x, D.a₀_filtration_preserving n x hx⟩ := by
  intro n x hx
  obtain ⟨u, hu_fil, hu_proj⟩ := D.proj₀_filtration_surj n x hx
  have hcompat := D.gr_a₀_compat_UEA n u hu_fil (hu_proj ▸ hx)
  have hq_eq : (⟨D.proj₀ u, hu_proj ▸ hx⟩ : { y : D.U₀.carrier // y ∈ D.filtration_U₀ n }) =
    ⟨x, hx⟩ := by
    simp only [Subtype.mk.injEq]; exact hu_proj
  rw [hq_eq] at hcompat
  have h_a₀_eq : D.a₀ x = D.actionMap u := by
    rw [← hu_proj, D.a₀_factors]
  rw [hcompat]
  congr 1
  exact Subtype.ext h_a₀_eq.symm

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[a₀_surj_of_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.a₀_surj_of_structure (D : BBDataZero) :
  Function.Surjective D.a₀ := by
  suffices h : ∀ n (y : D.DF.carrier), y ∈ D.filtration_DF n →
    ∃ x : D.U₀.carrier, x ∈ D.filtration_U₀ n ∧ D.a₀ x = y by
    intro y; obtain ⟨n, hn⟩ := D.filtration_DF_exhaustive y
    exact ⟨_, (h n y hn).choose_spec.2⟩
  intro n; induction n with
  | zero =>
    intro y hy
    obtain ⟨u, hu, hpu, hq⟩ := D.gr_a₀_approx_surj 0 y hy
    refine ⟨D.proj₀ u, hpu, ?_⟩
    have ha₀ : D.a₀ (D.proj₀ u) = D.actionMap u := D.a₀_factors u
    have hmem : D.actionMap u ∈ D.filtration_DF 0 := D.actionMap_filtration_preserving 0 u hu
    have hmem' : D.a₀ (D.proj₀ u) ∈ D.filtration_DF 0 := ha₀ ▸ hmem
    have hsub : y - D.a₀ (D.proj₀ u) ∈ D.filtration_DF 0 := (D.filtration_DF 0).sub_mem hy hmem'
    have hqs := D.quotient_DF_sub 0 y (D.a₀ (D.proj₀ u)) hy hmem' hsub
    have hq' : D.quotient_DF 0 ⟨D.a₀ (D.proj₀ u), hmem'⟩ = D.quotient_DF 0 ⟨y, hy⟩ := by
      have : D.quotient_DF 0 ⟨D.a₀ (D.proj₀ u), hmem'⟩ =
        D.quotient_DF 0 ⟨D.actionMap u, hmem⟩ := by
        congr 1; exact Subtype.ext ha₀
      rw [this]; exact hq
    have hzero : D.quotient_DF 0 ⟨y - D.a₀ (D.proj₀ u), hsub⟩ = 0 := by rw [hqs, hq', sub_self]
    have hbot := (D.quotient_DF_ker 0 _ hsub).mp hzero
    simp only [filtPred, Submodule.mem_bot] at hbot
    exact (sub_eq_zero.mp hbot).symm
  | succ n ih =>
    intro y hy
    obtain ⟨u, hu, hpu, hq⟩ := D.gr_a₀_approx_surj (n+1) y hy
    have ha₀ : D.a₀ (D.proj₀ u) = D.actionMap u := D.a₀_factors u
    have hmem : D.actionMap u ∈ D.filtration_DF (n+1) := D.actionMap_filtration_preserving (n+1) u hu
    have hmem' : D.a₀ (D.proj₀ u) ∈ D.filtration_DF (n+1) := ha₀ ▸ hmem
    have hsub : y - D.a₀ (D.proj₀ u) ∈ D.filtration_DF (n+1) := (D.filtration_DF (n+1)).sub_mem hy hmem'
    have hqs := D.quotient_DF_sub (n+1) y (D.a₀ (D.proj₀ u)) hy hmem' hsub
    have hq' : D.quotient_DF (n+1) ⟨D.a₀ (D.proj₀ u), hmem'⟩ = D.quotient_DF (n+1) ⟨y, hy⟩ := by
      have : D.quotient_DF (n+1) ⟨D.a₀ (D.proj₀ u), hmem'⟩ =
        D.quotient_DF (n+1) ⟨D.actionMap u, hmem⟩ := by
        congr 1; exact Subtype.ext ha₀
      rw [this]; exact hq
    have hzero : D.quotient_DF (n+1) ⟨y - D.a₀ (D.proj₀ u), hsub⟩ = 0 := by rw [hqs, hq', sub_self]
    have hresid := (D.quotient_DF_ker (n+1) _ hsub).mp hzero
    simp only [filtPred] at hresid
    obtain ⟨x', hx', hx'eq⟩ := ih _ hresid
    refine ⟨D.proj₀ u + x', Submodule.add_mem _ hpu (D.filtration_U₀_mono (Nat.le_succ n) hx'), ?_⟩
    rw [map_add, hx'eq, ha₀, add_sub_cancel]

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataZero.actionMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.actionMap_surjective
  {D : BBDataZero} :
-- imply
  Function.Surjective D.actionMap := by
-- proof
  intro y
  obtain ⟨u, hu⟩ := D.a₀_surj_of_structure y
  obtain ⟨x, hx⟩ := D.proj₀_surjective u
  exact ⟨x, by rw [← D.a₀_factors, hx, hu]⟩

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_a₀_eq_symbolOfAction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.gr_a₀_eq_symbolOfAction (D : BBDataZero) :
  ∀ x ∈ D.generators_grU₀_deg1, D.gr_a₀ x = D.symbolOfAction x :=
  D.gr_a₀_eq_symbolOfAction_field

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataZero.incl_p_star_eq_symbolOfAction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.incl_p_star_eq_symbolOfAction
  {D : BBDataZero} :
-- imply
  ∀ x ∈ D.generators_grU₀_deg1, (D.incl_TstarF.comp D.p_star) x = D.symbolOfAction x :=
-- proof
  D.incl_p_star_eq_symbolOfAction_field

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_a₀_step_down](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.gr_a₀_step_down (D : BBDataZero) :
  Function.Injective D.gr_a₀ →
    ∀ n (x : D.U₀.carrier), x ∈ D.filtration_U₀ n →
      D.a₀ x ∈ filtPred D.filtration_DF n → x ∈ filtPred D.filtration_U₀ n := by
  intro h_inj n x hx ha₀x
  have ha₀x_n : D.a₀ x ∈ D.filtration_DF n := D.a₀_filtration_preserving n x hx
  have hq_DF : D.quotient_DF n ⟨D.a₀ x, ha₀x_n⟩ = 0 :=
    (D.quotient_DF_ker n (D.a₀ x) ha₀x_n).mpr ha₀x
  have hcompat := D.gr_a₀_compat n x hx
  have hgr_zero : D.gr_a₀ (D.quotient_U₀ n ⟨x, hx⟩) = 0 := by
    rw [hcompat, hq_DF]
  have hq_zero : D.quotient_U₀ n ⟨x, hx⟩ = 0 := by
    have h0 : D.gr_a₀ 0 = 0 := map_zero D.gr_a₀
    rw [← h0] at hgr_zero
    exact h_inj hgr_zero
  exact (D.quotient_U₀_ker n x hx).mp hq_zero

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[quotient_surj_from_a₀](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.quotient_surj_from_a₀ (D : BBDataZero) :
  Function.Surjective D.a₀ →
  ∀ (n : ℕ) (y : D.DF.carrier) (hy : y ∈ D.filtration_DF n),
    ∃ x : D.U₀.carrier, ∃ hx : x ∈ D.filtration_U₀ n,
      D.quotient_DF n ⟨D.a₀ x, D.a₀_filtration_preserving n x hx⟩ = D.quotient_DF n ⟨y, hy⟩ := by
  intro _h_surj n y hy
  obtain ⟨u, hu, hpu, hq⟩ := D.gr_a₀_approx_surj n y hy
  refine ⟨D.proj₀ u, hpu, ?_⟩
  have ha₀_eq : D.a₀ (D.proj₀ u) = D.actionMap u := D.a₀_factors u
  have : D.quotient_DF n ⟨D.a₀ (D.proj₀ u), D.a₀_filtration_preserving n (D.proj₀ u) hpu⟩ =
    D.quotient_DF n ⟨D.actionMap u, D.actionMap_filtration_preserving n u hu⟩ := by
    congr 1; exact Subtype.ext ha₀_eq
  rwa [this]

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_a₀_step_up](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.gr_a₀_step_up (D : BBDataZero) :
  Function.Surjective D.a₀ →
    ∀ n (y : D.DF.carrier), y ∈ D.filtration_DF n →
      ∃ x, x ∈ D.filtration_U₀ n ∧ y - D.a₀ x ∈ filtPred D.filtration_DF n := by
  intro h_surj n y hy
  obtain ⟨x, hx, hq_eq⟩ := D.quotient_surj_from_a₀ h_surj n y hy
  refine ⟨x, hx, ?_⟩
  have ha₀x_n : D.a₀ x ∈ D.filtration_DF n := D.a₀_filtration_preserving n x hx
  have hy_sub_n : y - D.a₀ x ∈ D.filtration_DF n :=
    (D.filtration_DF n).sub_mem hy ha₀x_n
  have hsub := D.quotient_DF_sub n y (D.a₀ x) hy ha₀x_n hy_sub_n
  have hq_zero : D.quotient_DF n ⟨y - D.a₀ x, hy_sub_n⟩ = 0 := by
    rw [hsub, hq_eq, sub_self]
  exact (D.quotient_DF_ker n (y - D.a₀ x) hy_sub_n).mp hq_zero

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_a₀_surj_of_levelwise_surj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataZero.gr_a₀_surj_of_levelwise_surj (D : BBDataZero) :
  (∀ n (y : D.DF.carrier), y ∈ D.filtration_DF n →
    ∃ x, x ∈ D.filtration_U₀ n ∧ D.a₀ x = y) →
  Function.Surjective D.gr_a₀ := by
  intro h z
  obtain ⟨n, y, hy, hyz⟩ := D.quotient_DF_surj z
  obtain ⟨x, hx, hax⟩ := h n y hy
  refine ⟨D.quotient_U₀ n ⟨x, hx⟩, ?_⟩
  rw [D.gr_a₀_compat n x hx]
  subst hax
  exact hyz

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[incl_TstarF_inj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma incl_TstarF_inj
  {D : BBDataZero} :
-- imply
  Function.Injective D.incl_TstarF :=
-- proof
  D.symbol_proj_left_inv.injective

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[a₀_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma a₀_factorization (D : BBDataZero) :
  ∀ (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra),
    D.a₀ (D.proj₀ x) = D.actionMap x :=
  D.a₀_factors

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[a₀_surj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma a₀_surj (D : BBDataZero) : Function.Surjective D.a₀ := by
  intro y
  obtain ⟨x, hx⟩ := D.actionMap_surjective y
  exact ⟨D.proj₀ x, by rw [D.a₀_factors]; exact hx⟩

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_a₀_eq_on_deg1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma gr_a₀_eq_on_deg1 (D : BBDataZero) :
  ∀ x ∈ D.generators_grU₀_deg1,
    D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x := by
  intro x hx
  have h1 : D.gr_a₀ x = D.symbolOfAction x := D.gr_a₀_eq_symbolOfAction x hx
  have h2 : (D.incl_TstarF.comp D.p_star) x = D.symbolOfAction x :=
    D.incl_p_star_eq_symbolOfAction x hx
  exact h1.trans h2.symm

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[a₀_comp_proj₀](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma a₀_comp_proj₀ (D : BBDataZero)
  (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra) :
  D.a₀ (D.proj₀ x) = D.actionMap x :=
  a₀_factorization D x

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_a₀_eq_on_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma gr_a₀_eq_on_generators (D : BBDataZero) :
  ∀ x ∈ D.generators_grU₀, D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x := by
  intro x hx
  obtain h_deg0 | h_deg1 := D.generators_grU₀_decomp hx
  ·
    obtain ⟨r, rfl⟩ := h_deg0
    simp [AlgHom.commutes]
  ·
    exact gr_a₀_eq_on_deg1 D x h_deg1

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[incl_TstarF_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma incl_TstarF_injective
  {D : BBDataZero} :
-- imply
  Function.Injective D.incl_TstarF :=
-- proof
  incl_TstarF_inj D

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[filtered_surj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma filtered_surj
  {D : BBDataZero} :
-- imply
  Function.Surjective D.a₀ → Function.Surjective D.gr_a₀ := by
-- proof
  intro h_surj
  apply D.gr_a₀_surj_of_levelwise_surj
  have step_up := D.gr_a₀_step_up h_surj
  intro n
  induction n with
  | zero =>
    intro y hy
    obtain ⟨x, hx_mem, hresid⟩ := step_up 0 y hy
    simp only [filtPred, Submodule.mem_bot] at hresid
    exact ⟨x, hx_mem, (sub_eq_zero.mp hresid).symm⟩
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx_mem, hresid⟩ := step_up (n + 1) y hy
    simp only [filtPred] at hresid
    obtain ⟨x', hx'_mem, hx'_eq⟩ := ih (y - D.a₀ x) hresid
    refine ⟨x + x', ?_, ?_⟩
    · exact Submodule.add_mem _ hx_mem
      (D.filtration_U₀_mono (Nat.le_succ n) hx'_mem)
    · rw [map_add, hx'_eq, add_sub_cancel]

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_a₀_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma gr_a₀_surjective (D : BBDataZero) :
  Function.Surjective D.gr_a₀ :=
  filtered_surj D (a₀_surj D)

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[thm_29_1_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma thm_29_1_factorization
  {D : BBDataZero} :
-- imply
  D.actionMap = D.a₀.comp D.proj₀ := by
-- proof
  ext x
  show D.actionMap (UniversalEnvelopingAlgebra.ι ℂ x) =
    D.a₀ (D.proj₀ (UniversalEnvelopingAlgebra.ι ℂ x))
  exact (a₀_comp_proj₀ D (UniversalEnvelopingAlgebra.ι ℂ x)).symm

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[thm_29_1_gr_eq_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma thm_29_1_gr_eq_pullback
  {D : BBDataZero} :
-- imply
  D.gr_a₀ = D.incl_TstarF.comp D.p_star := by
-- proof
  ext x
  have hx : x ∈ Algebra.adjoin ℂ D.generators_grU₀ := by
    rw [D.grU₀_generated]; exact Algebra.mem_top
  exact Algebra.adjoin_induction
    (p := fun x _ => D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x)
    (fun y hy => gr_a₀_eq_on_generators D y hy)
    (fun r => by simp [AlgHom.commutes])
    (fun a b _ _ ha hb => by simp [map_add, ha, hb])
    (fun a b _ _ ha hb => by simp [map_mul, ha, hb])
    hx

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[thm_29_1_grDF_eq_O_TstarF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma thm_29_1_grDF_eq_O_TstarF
  {D : BBDataZero} :
-- imply
  Function.Bijective D.incl_TstarF := by
-- proof
  constructor
  ·
    exact incl_TstarF_injective D
  ·
    have h_gr_surj : Function.Surjective D.gr_a₀ := gr_a₀_surjective D
    have h_eq := thm_29_1_gr_eq_pullback D
    intro y
    obtain ⟨x, hx⟩ := h_gr_surj y
    have : D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x := by
      rw [h_eq]
    rw [this] at hx
    exact ⟨D.p_star x, hx⟩

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[filtered_bij](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma filtered_bij
  {D : BBDataZero} :
-- imply
  Function.Bijective D.gr_a₀ → Function.Bijective D.a₀ := by
-- proof
  intro hgr_bij
  refine ⟨?_, a₀_surj D⟩
  have step_down := D.gr_a₀_step_down hgr_bij.1
  intro x y hxy
  suffices h : x - y = 0 by exact sub_eq_zero.mp h
  set z := x - y
  have hz : D.a₀ z = 0 := by simp [z, map_sub, hxy]
  obtain ⟨n, hn⟩ := D.filtration_U₀_exhaustive z
  induction n with
  | zero =>
    have h1 : D.a₀ z ∈ filtPred D.filtration_DF 0 := by
      simp only [filtPred, Submodule.mem_bot]; exact hz
    have h2 := step_down 0 z hn h1
    simp only [filtPred, Submodule.mem_bot] at h2
    exact h2
  | succ n ih =>
    have h1 : D.a₀ z ∈ filtPred D.filtration_DF (n + 1) := by
      simp only [filtPred]; rw [hz]; exact Submodule.zero_mem _
    have h2 := step_down (n + 1) z hn h1
    simp only [filtPred] at h2
    exact ih h2

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[thm_29_1_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma thm_29_1_iso
  {D : BBDataZero} :
-- imply
  Function.Bijective D.a₀ := by
-- proof
  apply filtered_bij
  rw [thm_29_1_gr_eq_pullback D]
  exact (thm_29_1_grDF_eq_O_TstarF D).comp D.p_star_bijective

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataTwisted.aOfWeight_factors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataTwisted.aOfWeight_factors
  {D : BBDataTwisted} :
-- imply
  ∀ (mu : D.WeightSpace) (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra), D.aOfWeight mu (D.projOfWeight mu x) = D.actionMapOfWeight mu x :=
-- proof
  D.aOfWeight_factors_field

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataTwisted.actionMapOfWeight_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataTwisted.actionMapOfWeight_surjective
  {D : BBDataTwisted} :
-- imply
  ∀ (mu : D.WeightSpace), Function.Surjective (D.actionMapOfWeight mu) :=
-- proof
  D.actionMapOfWeight_surjective_field

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataTwisted.gr_aOfWeight_eq_symbolOfAction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataTwisted.gr_aOfWeight_eq_symbolOfAction
  {D : BBDataTwisted} :
-- imply
  ∀ (mu : D.WeightSpace) (x : (D.grUOfWeight mu).carrier), x ∈ D.generators_grUOfWeight_deg1 mu → D.gr_aOfWeight mu x = D.symbolOfActionOfWeight mu x :=
-- proof
  D.gr_aOfWeight_eq_symbolOfAction_field

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataTwisted.incl_p_star_eq_symbolOfActionOfWeight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataTwisted.incl_p_star_eq_symbolOfActionOfWeight
  {D : BBDataTwisted} :
-- imply
  ∀ (mu : D.WeightSpace) (x : (D.grUOfWeight mu).carrier), x ∈ D.generators_grUOfWeight_deg1 mu → (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) x = D.symbolOfActionOfWeight mu x :=
-- proof
  D.incl_p_star_eq_symbolOfActionOfWeight_field

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataTwisted.gr_aOfWeight_step_down](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataTwisted.gr_aOfWeight_step_down
  {D : BBDataTwisted} :
-- imply
  ∀ mu, Function.Injective (D.gr_aOfWeight mu) → ∀ n (x : (D.UOfWeight mu).carrier), x ∈ D.filtration_UOfWeight mu n → D.aOfWeight mu x ∈ filtPred (D.filtration_DOfWeight mu) n → x ∈ filtPred (D.filtration_UOfWeight mu) n := by
-- proof
  intro mu h_inj n x hx ha_x
  have ha_x_n : D.aOfWeight mu x ∈ D.filtration_DOfWeight mu n :=
    D.aOfWeight_filtration_preserving mu n x hx
  have hq_D : D.quotient_DOfWeight mu n ⟨D.aOfWeight mu x, ha_x_n⟩ = 0 :=
    (D.quotient_DOfWeight_ker mu n (D.aOfWeight mu x) ha_x_n).mpr ha_x
  have hcompat := D.gr_aOfWeight_compat mu n x hx
  have hgr_zero : D.gr_aOfWeight mu (D.quotient_UOfWeight mu n ⟨x, hx⟩) = 0 := by
    rw [hcompat, hq_D]
  have hq_zero : D.quotient_UOfWeight mu n ⟨x, hx⟩ = 0 := by
    have h0 : D.gr_aOfWeight mu 0 = 0 := map_zero (D.gr_aOfWeight mu)
    rw [← h0] at hgr_zero
    exact h_inj hgr_zero
  exact (D.quotient_UOfWeight_ker mu n x hx).mp hq_zero

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataTwisted.quotient_surj_from_aOfWeight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataTwisted.quotient_surj_from_aOfWeight
  {D : BBDataTwisted} :
-- imply
  ∀ mu, Function.Surjective (D.aOfWeight mu) → ∀ (n : ℕ) (y : (D.DOfWeight mu).carrier) (hy : y ∈ D.filtration_DOfWeight mu n), ∃ x : (D.UOfWeight mu).carrier, ∃ hx : x ∈ D.filtration_UOfWeight mu n, D.quotient_DOfWeight mu n ⟨D.aOfWeight mu x, D.aOfWeight_filtration_preserving mu n x hx⟩ = D.quotient_DOfWeight mu n ⟨y, hy⟩ := by
-- proof
  intro mu _h_surj n y hy
  exact D.gr_aOfWeight_approx_surj mu n y hy

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataTwisted.gr_aOfWeight_step_up](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataTwisted.gr_aOfWeight_step_up
  {D : BBDataTwisted} :
-- imply
  ∀ mu, Function.Surjective (D.aOfWeight mu) → ∀ n (y : (D.DOfWeight mu).carrier), y ∈ D.filtration_DOfWeight mu n → ∃ x, x ∈ D.filtration_UOfWeight mu n ∧ y - D.aOfWeight mu x ∈ filtPred (D.filtration_DOfWeight mu) n := by
-- proof
  intro mu h_surj n y hy
  obtain ⟨x, hx, hq_eq⟩ := D.quotient_surj_from_aOfWeight mu h_surj n y hy
  refine ⟨x, hx, ?_⟩
  have ha_x_n : D.aOfWeight mu x ∈ D.filtration_DOfWeight mu n :=
    D.aOfWeight_filtration_preserving mu n x hx
  have hy_sub_n : y - D.aOfWeight mu x ∈ D.filtration_DOfWeight mu n :=
    (D.filtration_DOfWeight mu n).sub_mem hy ha_x_n
  have hsub := D.quotient_DOfWeight_sub mu n y (D.aOfWeight mu x) hy ha_x_n hy_sub_n
  have hq_zero : D.quotient_DOfWeight mu n ⟨y - D.aOfWeight mu x, hy_sub_n⟩ = 0 := by
    rw [hsub, hq_eq, sub_self]
  exact (D.quotient_DOfWeight_ker mu n (y - D.aOfWeight mu x) hy_sub_n).mp hq_zero

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[BBDataTwisted.gr_aOfWeight_surj_of_levelwise_surj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma BBDataTwisted.gr_aOfWeight_surj_of_levelwise_surj
  {D : BBDataTwisted} :
-- imply
  ∀ mu, (∀ n (y : (D.DOfWeight mu).carrier), y ∈ D.filtration_DOfWeight mu n → ∃ x, x ∈ D.filtration_UOfWeight mu n ∧ D.aOfWeight mu x = y) → Function.Surjective (D.gr_aOfWeight mu) := by
-- proof
  intro mu h z
  obtain ⟨n, y, hy, hyz⟩ := D.quotient_DOfWeight_surj mu z
  obtain ⟨x, hx, hax⟩ := h n y hy
  refine ⟨D.quotient_UOfWeight mu n ⟨x, hx⟩, ?_⟩
  rw [D.gr_aOfWeight_compat mu n x hx]
  subst hax
  exact hyz

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[aOfWeight_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma aOfWeight_factorization
  {D : BBDataTwisted} :
-- imply
  ∀ (mu : D.WeightSpace) (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra), D.aOfWeight mu (D.projOfWeight mu x) = D.actionMapOfWeight mu x :=
-- proof
  D.aOfWeight_factors

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[incl_TstarFOfWeight_inj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma incl_TstarFOfWeight_inj
  {D : BBDataTwisted} :
-- imply
  ∀ (mu : D.WeightSpace), Function.Injective (D.incl_TstarFOfWeight mu) :=
-- proof
  fun mu => (D.symbol_projOfWeight_left_inv mu).injective

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[aOfWeight_surj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma aOfWeight_surj
  {D : BBDataTwisted} :
-- imply
  ∀ (mu : D.WeightSpace), Function.Surjective (D.aOfWeight mu) := by
-- proof
  intro mu y
  obtain ⟨x, hx⟩ := D.actionMapOfWeight_surjective mu y
  exact ⟨D.projOfWeight mu x, by rw [D.aOfWeight_factors]; exact hx⟩

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_aOfWeight_eq_on_deg1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma gr_aOfWeight_eq_on_deg1
  {D : BBDataTwisted} :
-- imply
  ∀ (mu : D.WeightSpace) (x : (D.grUOfWeight mu).carrier), x ∈ D.generators_grUOfWeight_deg1 mu → D.gr_aOfWeight mu x = (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) x := by
-- proof
  intro mu x hx
  have h1 : D.gr_aOfWeight mu x = D.symbolOfActionOfWeight mu x :=
    D.gr_aOfWeight_eq_symbolOfAction mu x hx
  have h2 : (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) x =
    D.symbolOfActionOfWeight mu x :=
    D.incl_p_star_eq_symbolOfActionOfWeight mu x hx
  exact h1.trans h2.symm

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[aOfWeight_comp_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma aOfWeight_comp_proj
  {D : BBDataTwisted}
  {mu : D.WeightSpace}
  {x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra} :
-- imply
  D.aOfWeight mu (D.projOfWeight mu x) = D.actionMapOfWeight mu x :=
-- proof
  aOfWeight_factorization D mu x

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_aOfWeight_eq_on_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma gr_aOfWeight_eq_on_generators
  {D : BBDataTwisted}
  {mu : D.WeightSpace}
  {x : (D.grUOfWeight mu).carrier} :
-- imply
  x ∈ D.generators_grUOfWeight mu → D.gr_aOfWeight mu x = (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) x := by
-- proof
  intro hx
  obtain h_deg0 | h_deg1 := D.generators_grUOfWeight_decomp mu hx
  ·
    obtain ⟨r, rfl⟩ := h_deg0
    simp [AlgHom.commutes]
  ·
    exact gr_aOfWeight_eq_on_deg1 D mu x h_deg1

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[incl_TstarFOfWeight_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma incl_TstarFOfWeight_injective
  {D : BBDataTwisted}
  {mu : D.WeightSpace} :
-- imply
  Function.Injective (D.incl_TstarFOfWeight mu) :=
-- proof
  incl_TstarFOfWeight_inj D mu

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[thm_29_6_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma thm_29_6_factorization
  {D : BBDataTwisted}
  {mu : D.WeightSpace} :
-- imply
  D.actionMapOfWeight mu = (D.aOfWeight mu).comp (D.projOfWeight mu) := by
-- proof
  ext x
  show D.actionMapOfWeight mu (UniversalEnvelopingAlgebra.ι ℂ x) =
    D.aOfWeight mu (D.projOfWeight mu (UniversalEnvelopingAlgebra.ι ℂ x))
  exact (aOfWeight_comp_proj D mu (UniversalEnvelopingAlgebra.ι ℂ x)).symm

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[thm_29_6_gr_eq_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma thm_29_6_gr_eq_pullback
  {D : BBDataTwisted}
  {mu : D.WeightSpace} :
-- imply
  D.gr_aOfWeight mu = (D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu) := by
-- proof
  ext x
  have hx : x ∈ Algebra.adjoin ℂ (D.generators_grUOfWeight mu) := by
    rw [D.grUOfWeight_generated mu]; exact Algebra.mem_top
  exact Algebra.adjoin_induction
    (p := fun x _ => D.gr_aOfWeight mu x = ((D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu)) x)
    (fun y hy => gr_aOfWeight_eq_on_generators D mu y hy)
    (fun r => by simp [AlgHom.commutes])
    (fun a b _ _ ha hb => by simp [map_add, ha, hb])
    (fun a b _ _ ha hb => by simp [map_mul, ha, hb])
    hx

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[filtered_surj_twisted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma filtered_surj_twisted
  {D : BBDataTwisted}
  {mu : D.WeightSpace} :
-- imply
  Function.Surjective (D.aOfWeight mu) → Function.Surjective (D.gr_aOfWeight mu) := by
-- proof
  intro h_surj
  apply D.gr_aOfWeight_surj_of_levelwise_surj mu
  have step_up := D.gr_aOfWeight_step_up mu h_surj
  intro n
  induction n with
  | zero =>
    intro y hy
    obtain ⟨x, hx_mem, hresid⟩ := step_up 0 y hy
    simp only [filtPred, Submodule.mem_bot] at hresid
    exact ⟨x, hx_mem, (sub_eq_zero.mp hresid).symm⟩
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx_mem, hresid⟩ := step_up (n + 1) y hy
    simp only [filtPred] at hresid
    obtain ⟨x', hx'_mem, hx'_eq⟩ := ih (y - D.aOfWeight mu x) hresid
    refine ⟨x + x', ?_, ?_⟩
    · exact Submodule.add_mem _ hx_mem
      (D.filtration_UOfWeight_mono mu (Nat.le_succ n) hx'_mem)
    · rw [map_add, hx'_eq, add_sub_cancel]

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[gr_aOfWeight_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma gr_aOfWeight_surjective
  {D : BBDataTwisted}
  {mu : D.WeightSpace} :
-- imply
  Function.Surjective (D.gr_aOfWeight mu) :=
-- proof
  filtered_surj_twisted D mu (aOfWeight_surj D mu)

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[thm_29_6_grDF_eq_O_TstarF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma thm_29_6_grDF_eq_O_TstarF
  {D : BBDataTwisted}
  {mu : D.WeightSpace} :
-- imply
  Function.Bijective (D.incl_TstarFOfWeight mu) := by
-- proof
  constructor
  · exact incl_TstarFOfWeight_injective D mu
  ·
    have h_gr_surj : Function.Surjective (D.gr_aOfWeight mu) := gr_aOfWeight_surjective D mu
    have h_eq := thm_29_6_gr_eq_pullback D mu
    intro y
    obtain ⟨x, hx⟩ := h_gr_surj y
    have : D.gr_aOfWeight mu x = ((D.incl_TstarFOfWeight mu).comp (D.p_starOfWeight mu)) x := by
      rw [h_eq]
    rw [this] at hx
    exact ⟨D.p_starOfWeight mu x, hx⟩

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[filtered_bijOfWeight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma filtered_bijOfWeight
  {D : BBDataTwisted}
  {mu : D.WeightSpace} :
-- imply
  Function.Bijective (D.gr_aOfWeight mu) → Function.Bijective (D.aOfWeight mu) := by
-- proof
  intro hgr_bij
  refine ⟨?_, aOfWeight_surj D mu⟩
  have step_down := D.gr_aOfWeight_step_down mu hgr_bij.1
  intro x y hxy
  suffices h : x - y = 0 by exact sub_eq_zero.mp h
  set z := x - y
  have hz : D.aOfWeight mu z = 0 := by simp [z, map_sub, hxy]
  obtain ⟨n, hn⟩ := D.filtration_UOfWeight_exhaustive mu z
  induction n with
  | zero =>
    have h1 : D.aOfWeight mu z ∈ filtPred (D.filtration_DOfWeight mu) 0 := by
      simp only [filtPred, Submodule.mem_bot]; exact hz
    have h2 := step_down 0 z hn h1
    simp only [filtPred, Submodule.mem_bot] at h2
    exact h2
  | succ n ih =>
    have h1 : D.aOfWeight mu z ∈ filtPred (D.filtration_DOfWeight mu) (n + 1) := by
      simp only [filtPred]; rw [hz]; exact Submodule.zero_mem _
    have h2 := step_down (n + 1) z hn h1
    simp only [filtPred] at h2
    exact ih h2

end BeilinsonBernstein

namespace BeilinsonBernstein

/--
[thm_29_6_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
lemma thm_29_6_iso
  {D : BBDataTwisted}
  {mu : D.WeightSpace} :
-- imply
  Function.Bijective (D.aOfWeight mu) := by
-- proof
  apply filtered_bijOfWeight
  rw [thm_29_6_gr_eq_pullback D mu]
  exact (thm_29_6_grDF_eq_O_TstarF D mu).comp (D.p_starOfWeight_bijective mu)
end


/--
[BBDataZero.a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma a_eq
  {D : BBDataZero} :
-- imply
  ∀ (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra), D.a₀ (D.proj₀ x) = D.actionMap x := by
-- proof
  apply BeilinsonBernstein.BBDataZero.a D

/--
[BBDataZero.a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma a_eq_2
  {D : BBDataZero} :
-- imply
  ∀ n (x : D.U₀.carrier), x ∈ D.filtration_U₀ n → D.a₀ x ∈ D.filtration_DF n := by
-- proof
  apply BeilinsonBernstein.BBDataZero.a D

/--
[BBDataZero.gr_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma gr_a_eq
  {D : BBDataZero} :
-- imply
  ∀ n (x : D.U₀.carrier) (hx : x ∈ D.filtration_U₀ n), D.gr_a₀ (D.quotient_U₀ n ⟨x, hx⟩) = D.quotient_DF n ⟨D.a₀ x, D.a₀_filtration_preserving n x hx⟩ := by
-- proof
  apply BeilinsonBernstein.BBDataZero.gr_a D

/--
[BBDataZero.a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma a_eq_3
  {D : BBDataZero} :
-- imply
  Function.Surjective D.a₀ := by
-- proof
  apply BeilinsonBernstein.BBDataZero.a D

/--
[BBDataZero.gr_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma gr_a_eq_2
  {D : BBDataZero} :
-- imply
  ∀ x ∈ D.generators_grU₀_deg1, D.gr_a₀ x = D.symbolOfAction x := by
-- proof
  apply BeilinsonBernstein.BBDataZero.gr_a D

/--
[BBDataZero.gr_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma gr_a_eq_3
  {D : BBDataZero} :
-- imply
  Function.Injective D.gr_a₀ → ∀ n (x : D.U₀.carrier), x ∈ D.filtration_U₀ n → D.a₀ x ∈ filtPred D.filtration_DF n → x ∈ filtPred D.filtration_U₀ n := by
-- proof
  apply BeilinsonBernstein.BBDataZero.gr_a D

/--
[BBDataZero.quotient_surj_from_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma quotient_surj_from_a_eq
  {D : BBDataZero} :
-- imply
  Function.Surjective D.a₀ → ∀ (n : ℕ) (y : D.DF.carrier) (hy : y ∈ D.filtration_DF n), ∃ x : D.U₀.carrier, ∃ hx : x ∈ D.filtration_U₀ n, D.quotient_DF n ⟨D.a₀ x, D.a₀_filtration_preserving n x hx⟩ = D.quotient_DF n ⟨y, hy⟩ := by
-- proof
  apply BeilinsonBernstein.BBDataZero.quotient_surj_from_a D

/--
[BBDataZero.gr_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma gr_a_eq_4
  {D : BBDataZero} :
-- imply
  Function.Surjective D.a₀ → ∀ n (y : D.DF.carrier), y ∈ D.filtration_DF n → ∃ x, x ∈ D.filtration_U₀ n ∧ y - D.a₀ x ∈ filtPred D.filtration_DF n := by
-- proof
  apply BeilinsonBernstein.BBDataZero.gr_a D

/--
[BBDataZero.gr_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma gr_a_eq_5
  {D : BBDataZero} :
-- imply
  (∀ n (y : D.DF.carrier), y ∈ D.filtration_DF n → ∃ x, x ∈ D.filtration_U₀ n ∧ D.a₀ x = y) → Function.Surjective D.gr_a₀ := by
-- proof
  apply BeilinsonBernstein.BBDataZero.gr_a D

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma a_eq_4
  {D : BBDataZero} :
-- imply
  ∀ (x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra), D.a₀ (D.proj₀ x) = D.actionMap x := by
-- proof
  apply BeilinsonBernstein.a D

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma a_eq_5
  {D : BBDataZero} :
-- imply
  Function.Surjective D.a₀ := by
-- proof
  apply BeilinsonBernstein.a D

/--
[gr_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma gr_a_eq_6
  {D : BBDataZero} :
-- imply
  ∀ x ∈ D.generators_grU₀_deg1, D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x := by
-- proof
  apply BeilinsonBernstein.gr_a D

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma a_eq_6
  {D : BBDataZero}
  {x : @UniversalEnvelopingAlgebra ℂ D.gLie _ D.instLieRing D.instLieAlgebra} :
-- imply
  D.a₀ (D.proj₀ x) = D.actionMap x := by
-- proof
  apply BeilinsonBernstein.a D x

/--
[gr_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma gr_a_eq_7
  {D : BBDataZero} :
-- imply
  ∀ x ∈ D.generators_grU₀, D.gr_a₀ x = (D.incl_TstarF.comp D.p_star) x := by
-- proof
  apply BeilinsonBernstein.gr_a D

/--
[gr_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean)
-/
@[path]
private lemma gr_a_eq_8
  {D : BBDataZero} :
-- imply
  Function.Surjective D.gr_a₀ := by
-- proof
  apply BeilinsonBernstein.gr_a D


-- created on 2026-10-23
