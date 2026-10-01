import Mathlib.GroupTheory.Perm.Fin
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma factorization_general
  {n : ℕ}
  {a : ℕ → ℤ}
-- given
  (_h : ((Finset.range n).image a).card = n) :
-- imply
  ∀ p ∈ {p : Fin n → ℤ | Finset.univ.image p = (Finset.range n).image a},
    ∃ b : Fin n → Fin n, p = fun k => a (((List.finRange n).map fun i => Equiv.swap i (b i)).prod k) := by
-- proof
  have lift0 : ∀ {m : ℕ} (l : List (Fin m)) (c : Fin m → Fin m),
      (l.map fun i => Equiv.swap i.succ (c i).succ).prod 0 = 0 := by
    intro m l c
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul, Function.comp_apply, ih]
      exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero _).symm
  have liftS : ∀ {m : ℕ} (l : List (Fin m)) (c : Fin m → Fin m) (x : Fin m),
      (l.map fun i => Equiv.swap i.succ (c i).succ).prod x.succ = ((l.map fun i => Equiv.swap i (c i)).prod x).succ := by
    intro m l c x
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul, Function.comp_apply, ih, List.map_cons, List.prod_cons,
        Equiv.Perm.coe_mul, Function.comp_apply]
      exact (Fin.succ_injective m).swap_apply _ _ _
  have helper : ∀ (m : ℕ) (σ : Equiv.Perm (Fin m)),
      ∃ b : Fin m → Fin m, σ = ((List.finRange m).map fun i => Equiv.swap i (b i)).prod := by
    intro m
    induction m with
    | zero => exact fun σ => ⟨Fin.elim0, Subsingleton.elim _ _⟩
    | succ m ih =>
      intro σ
      obtain ⟨⟨p, e⟩, rfl⟩ : ∃ pe, σ = Equiv.Perm.decomposeFin.symm pe :=
        ⟨_, (Equiv.symm_apply_apply _ σ).symm⟩
      obtain ⟨b', hb'⟩ := ih e
      refine ⟨Fin.cons p (fun i => (b' i).succ), ?_⟩
      rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
      simp only [Fin.cons_zero, Function.comp_def, Fin.cons_succ]
      ext y
      cases y using Fin.cases with
      | zero =>
        rw [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.coe_mul, Function.comp_apply, lift0,
          Equiv.swap_apply_left]
      | succ x =>
        rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.Perm.coe_mul, Function.comp_apply, liftS, ← hb']
  intro p hp
  have hp' : Finset.univ.image p = (Finset.range n).image a := hp
  have hmem : ∀ k, ∃ j : Fin n, a j = p k := by
    intro k
    have hk : p k ∈ (Finset.range n).image a := hp' ▸ Finset.mem_image_of_mem p (Finset.mem_univ k)
    obtain ⟨j, hj, e⟩ := Finset.mem_image.mp hk
    exact ⟨⟨j, Finset.mem_range.mp hj⟩, e⟩
  choose τ hτ using hmem
  have hpinj : Function.Injective p := by
    have hc : (Finset.univ.image p).card = (Finset.univ : Finset (Fin n)).card := by
      rw [hp', _h, Finset.card_univ, Fintype.card_fin]
    exact fun u v e => Finset.card_image_iff.mp hc (Finset.mem_coe.mpr (Finset.mem_univ u)) (Finset.mem_coe.mpr (Finset.mem_univ v)) e
  have hτinj : Function.Injective τ := fun u v e => hpinj (by rw [← hτ u, ← hτ v, e])
  obtain ⟨b, hb⟩ := helper n (Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτinj))
  refine ⟨b, funext fun k => ?_⟩
  rw [← hb]
  exact (hτ k).symm


-- created on 2020-11-01
