import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ContinuousLinearMap_exists_comp_torusEmb_eq_and_cylinder_noAtomicMass_of_box_noAtomicMass.lean)
-/
@[path]
private lemma main
  (d : ℕ)
  (XK : Set (Fin d → ℂ × ℂ))
  (emb : ContinuousMap (Fin d → AddCircle (1 : ℝ)) XK)
  (hemb : ∀ (θ : Fin d → AddCircle (1 : ℝ)) (i : Fin d), ((emb θ : XK) : Fin d → ℂ × ℂ) i = ((fourier 1 (θ i) : ℂ), (fourier (-1) (θ i) : ℂ)))
  (μ : ContinuousMap (Fin d → AddCircle (1 : ℝ)) ℂ →L[ℂ] ℂ)
  (hμ : ∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ), ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧ ∀ g : ContinuousMap (Fin d → AddCircle (1 : ℝ)) ℂ, (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) :
  -- imply
  ∃ Λ : ContinuousMap XK ℂ →L[ℂ] ℂ, (∀ h : ContinuousMap XK ℂ, Λ h = μ (h.comp emb)) ∧ ∀ (τ : Fin d → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : Fin d → Set (ℂ × ℂ), (∀ v ∈ (Finset.univ : Finset (Fin d)), IsOpen (U v) ∧ τ v ∈ U v) ∧ ∀ g : ContinuousMap XK ℂ, (∀ y : XK, (∃ v ∈ (Finset.univ : Finset (Fin d)), (y : Fin d → ℂ × ℂ) v ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε := by
  -- proof
  classical
  let compCLM : ContinuousMap XK ℂ →L[ℂ] ContinuousMap (Fin d → AddCircle (1 : ℝ)) ℂ :=
    { toFun := fun h => h.comp emb
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := ContinuousMap.continuous_precomp emb }
  refine ⟨μ.comp compCLM, fun h => rfl, ?_⟩
  intro τ ε hε
  let F : AddCircle (1 : ℝ) → ℂ × ℂ := fun t => ((fourier 1 t : ℂ), (fourier (-1) t : ℂ))
  have hFc : Continuous F := (fourier 1).continuous.prodMk (fourier (-1)).continuous
  have hFi : Function.Injective F := by
    intro a b h
    have h1 : (fourier 1 a : ℂ) = fourier 1 b := congrArg Prod.fst h
    rw [fourier_one, fourier_one] at h1
    apply AddCircle.injective_toCircle one_ne_zero (by exact_mod_cast h1)
  let τ' : Fin d → AddCircle (1 : ℝ) := fun i => if h : ∃ t, F t = τ i then h.choose else 0
  obtain ⟨U', hU'o, hU'g⟩ := hμ τ' ε hε
  let S : Fin d → Set (AddCircle (1 : ℝ)) := fun i => if (∃ t, F t = τ i) then (U' i)ᶜ else Set.univ
  have hSc : ∀ i, IsClosed (S i) := by
    intro i
    if h : ∃ t, F t = τ i then
      simp only [S, ite_eq_left h]
      apply (hU'o i).1.isClosed_compl
    else
      simp only [S, ite_eq_right h]
      apply isClosed_univ
  have hSU : ∀ (i : Fin d) (t : AddCircle (1 : ℝ)), t ∉ S i → t ∈ U' i := by
    intro i t ht
    if h : ∃ t, F t = τ i then
      simp only [S, ite_eq_left h, Set.mem_compl_iff, not_not] at ht
      apply ht
    else
      simp only [S, ite_eq_right h, Set.mem_univ, not_true_eq_false] at ht
  refine ⟨fun i => (F '' S i)ᶜ, ?_, ?_⟩
  ·
    intro i _
    refine ⟨((hSc i).isCompact.image hFc).isClosed.isOpen_compl, ?_⟩
    simp only [Set.mem_compl_iff]
    rintro ⟨t, ht, hti⟩
    if h : ∃ t, F t = τ i then
      have hτ' : F (τ' i) = τ i := by
        simp only [τ', dite_eq_left h]
        apply h.choose_spec
      have htt : t = τ' i := hFi (hti.trans hτ'.symm)
      simp only [S, ite_eq_left h, Set.mem_compl_iff] at ht
      apply ht (htt ▸ (hU'o i).2)
    else
      apply h ⟨t, hti⟩
  ·
    intro g hg0 hg1
    show ‖μ (g.comp emb)‖ < ε
    refine hU'g (g.comp emb) ?_ (fun θ => hg1 (emb θ))
    rintro θ ⟨i, hi⟩
    show g (emb θ) = 0
    apply hg0
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [hemb]
    simp only [Set.mem_compl_iff, not_not]
    refine ⟨θ i, ?_, rfl⟩
    by_contra hS
    apply hi (hSU i (θ i) hS)


-- created on 2026-10-20
