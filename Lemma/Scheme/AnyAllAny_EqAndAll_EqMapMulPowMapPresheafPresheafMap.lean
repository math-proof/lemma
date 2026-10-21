import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.lean)
-/
@[path]
private lemma main
  {Z : (Scheme : Type 1)} {r : ℕ} (V : Fin r → Z.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (w : ∀ i : Fin r, Fin r → (Z.presheaf.obj (op (V i))))
  (hW1 : ∀ i, w i i = 1)
  (hW2 : ∀ i j k : Fin r, Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
    Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
      Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
  (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j)
  (i₀ : Fin r) (g : (Z.presheaf.obj (op (V i₀)))) :
  ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : ∀ j : Fin r, (Z.presheaf.obj (op (V j))), t i₀ = g ∧
    ∀ j m : Fin r, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (t j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (t m) := by
  classical
  have res_res : ∀ {A B C : Z.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C) (x : (Z.presheaf.obj (op C))), Z.presheaf.map (homOfLE h₁).op (Z.presheaf.map (homOfLE h₂).op x) =
      Z.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro A B C h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have stepA : ∀ j : Fin r, ∃ (a : (Z.presheaf.obj (op (V j)))) (n : ℕ), Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op a =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    let _ : Algebra (Z.presheaf.obj (op (V j))) (Z.presheaf.obj (op (V j ⊓ V i₀))) :=
      (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op).hom.toAlgebra
    let _ : IsLocalization.Away (w j i₀) (Z.presheaf.obj (op (V j ⊓ V i₀))) :=
      (hV j).isLocalization_of_eq_basicOpen (w j i₀) (homOfLE inf_le_left) (hW3 j i₀).symm
    obtain ⟨⟨a, ⟨s, ⟨n, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (w j i₀))
      (Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g)
    refine ⟨a, n, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow] at h
    rw [← h, mul_comm]
  choose a₀ n₀ ha₀ using stepA
  let a : ∀ j : Fin r, (Z.presheaf.obj (op (V j))) := Function.update a₀ i₀ g
  let n : Fin r → ℕ := Function.update n₀ i₀ 0
  have ha : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (a j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n j *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    if hj : j = i₀ then
      subst hj
      simp only [a, n, Function.update_self, pow_zero, one_mul]
    else
      simp only [a, n, Function.update_of_ne hj]
      apply ha₀ j
  let k₁ : ℕ := Finset.univ.sup n
  have hn : ∀ j, n j ≤ k₁ := fun j => Finset.le_sup (f := n) (Finset.mem_univ j)
  let b : ∀ j : Fin r, (Z.presheaf.obj (op (V j))) := fun j => a j * w j i₀ ^ (k₁ - n j)
  have hb : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (b j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ k₁ *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    simp only [b, map_mul, map_pow, ha]
    rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' (hn j)]
  have hbi₀ : b i₀ = g := by
    simp only [b, a, n, Function.update_self, hW1, one_pow, mul_one]
  have stepB : ∀ j m : Fin r, ∃ e : ℕ, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀) ^ e *
      (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
          Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
    intro j m
    have hjm : IsAffineOpen (V j ⊓ V m) := by
      rw [← hW3 j m]
      apply (hV j).basicOpen (w j m)
    have hT : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) =
        Z.basicOpen (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)) := by
      rw [Scheme.basicOpen_res, hW3]
    let _ : Algebra (Z.presheaf.obj (op (V j ⊓ V m))) (Z.presheaf.obj (op ((V j ⊓ V m) ⊓ (V j ⊓ V i₀)))) :=
      (Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op).hom.toAlgebra
    let _ : IsLocalization.Away (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀))
      (Z.presheaf.obj (op ((V j ⊓ V m) ⊓ (V j ⊓ V i₀)))) :=
      hjm.isLocalization_of_eq_basicOpen _ (homOfLE inf_le_left) hT
    have hvan : Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op
      (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
          Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
      have e1 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_right : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V i₀)).op) (hb j)
      have e2 := congrArg (Z.presheaf.map (homOfLE
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V m ⊓ V i₀)).op) (hb m)
      have e3 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op) (hW2 j m i₀)
      simp only [map_sub, map_mul, map_pow, res_res] at e1 e2 e3 ⊢
      rw [e1, e2, e3]
      ring
    obtain ⟨⟨_, ⟨e, rfl⟩⟩, he⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)))
      (Z.presheaf.obj (op ((V j ⊓ V m) ⊓ (V j ⊓ V i₀)))) _).mp hvan
    exact ⟨e, he⟩
  choose e he using stepB
  let E : ℕ := Finset.univ.sup (fun jm : Fin r × Fin r => e jm.1 jm.2)
  have hE : ∀ j m, e j m ≤ E := fun j m =>
    Finset.le_sup (f := fun jm : Fin r × Fin r => e jm.1 jm.2) (Finset.mem_univ (j, m))
  refine ⟨k₁ + E, fun k hk => ⟨fun j => b j * w j i₀ ^ (k - k₁), ?_, ?_⟩⟩
  ·
    simp only [hbi₀, hW1, one_pow, mul_one]
  ·
    intro j m
    obtain ⟨E', hE'⟩ : ∃ E', k = k₁ + (e j m + E') := by
      refine ⟨k - k₁ - e j m, ?_⟩
      have := hE j m
      omega
    have hkk : k - k₁ = e j m + E' := by omega
    have c := hW2 j m i₀
    have d := he j m
    simp only [map_mul, map_pow, hkk]
    rw [hE']
    rw [c] at d ⊢
    linear_combination ((Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) *
      Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (w m i₀)) ^ E') * d


-- created on 2026-10-20
