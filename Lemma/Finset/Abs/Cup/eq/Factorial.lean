import sympy.sets.sets
import sympy.Basic
open Nat


@[path]
private lemma main
  {n : ℕ} :
-- imply
  {x : Fin n → ℕ | Finset.univ.image x = Finset.range n}.ncard = n ! := by
-- proof
  have hset : {x : Fin n → ℕ | Finset.univ.image x = Finset.range n} = Set.range (fun σ : Equiv.Perm (Fin n) => fun i => ((σ i : Fin n) : ℕ)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · intro h
      have hlt : ∀ i, x i < n := fun i => by
        have hi : x i ∈ Finset.univ.image x := Finset.mem_image_of_mem _ (Finset.mem_univ i)
        rw [h] at hi
        exact Finset.mem_range.mp hi
      have hinj : Function.Injective x := by
        have hc := Finset.card_image_iff.mp (show (Finset.univ.image x).card = (Finset.univ : Finset (Fin n)).card by rw [h]; simp)
        exact fun a b e => hc (by simp) (by simp) e
      have hf : Function.Injective (fun i => (⟨x i, hlt i⟩ : Fin n)) := fun a b e => hinj (congrArg Fin.val e)
      exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hf), rfl⟩
    · rintro ⟨σ, rfl⟩
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact (σ a).isLt
      · intro hy
        exact ⟨σ.symm ⟨y, hy⟩, by simp⟩
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin n) => fun i => ((σ i : Fin n) : ℕ)) :=
    fun σ τ e => Equiv.ext fun i => Fin.ext (congrFun e i)
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]


-- created on 2020-08-07
