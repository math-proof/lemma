import Def.LinearAlgebra.Matrix.Permutation
import Lemma.Matrix.GetDot_SwapMatrix.eq.Get
open Matrix
set_option maxHeartbeats 400000


private lemma ofFn_snoc
  {α : Type*} {m : ℕ} (f : Fin (m + 1) → α) :
  List.ofFn f = List.ofFn (fun i : Fin m => f i.castSucc) ++ [f (Fin.last m)] := by
  refine List.ext_getElem (by simp [List.length_ofFn]) ?_
  intro i h1 h2
  simp only [List.getElem_append, List.length_ofFn, List.getElem_ofFn]
  if hi : i < m then
    simp [hi]
  else
    have hi' : i < m + 1 := by simpa [List.length_ofFn] using h1
    have : i = m := Nat.eq_of_lt_succ_of_not_lt hi' hi
    simp [this, Fin.last]

@[path]
private lemma main
  [Semiring α]
  {n m : ℕ}
-- given
  (hmn : m ≤ n)
  (d : Fin m → Fin n)
  (x : Fin n → α) :
-- imply
  (fun k : Fin n =>
    x (Fin.foldl m (fun (σ : Equiv.Perm (Fin n)) (i : Fin m) =>
      σ * Equiv.swap (Fin.castLE hmn i) (d i)) 1 k)) =
  x ᵥ* (List.ofFn fun i : Fin m =>
    swapMatrix (α := α) (Fin.castLE hmn i) (d i)).prod := by
-- proof
  induction m with
  | zero =>
    simp only [Fin.foldl_zero, List.ofFn_zero, List.prod_nil, Equiv.Perm.one_apply,
      vecMul_one]
  | succ m ih =>
    let d' : Fin m → Fin n := fun i => d i.castSucc
    let hmn' : m ≤ n := Nat.le_of_succ_le hmn
    let P : Matrix (Fin n) (Fin n) α :=
      (List.ofFn fun i : Fin m =>
        swapMatrix (α := α) (Fin.castLE hmn' i) (d' i)).prod
    let W : Matrix (Fin n) (Fin n) α :=
      swapMatrix (α := α) (Fin.castLE hmn (Fin.last m)) (d (Fin.last m))
    have hcast (i : Fin m) :
      Fin.castLE hmn i.castSucc = Fin.castLE hmn' i := by
      ext
      simp
    have hfold :
      Fin.foldl (m + 1)
        (fun (σ : Equiv.Perm (Fin n)) (i : Fin (m + 1)) =>
          σ * Equiv.swap (Fin.castLE hmn i) (d i)) 1 =
        Fin.foldl m
          (fun (σ : Equiv.Perm (Fin n)) (i : Fin m) =>
            σ * Equiv.swap (Fin.castLE hmn' i) (d' i)) 1 *
          Equiv.swap (Fin.castLE hmn (Fin.last m)) (d (Fin.last m)) := by
      rw [Fin.foldl_succ_last]
      simp only [d']
      refine congrArg₂ (· * ·) ?_ rfl
      refine congrArg (fun f => Fin.foldl m f 1) ?_
      funext σ i
      rw [hcast]
    have hL :
      (List.ofFn fun i : Fin (m + 1) =>
        swapMatrix (α := α) (Fin.castLE hmn i) (d i)).prod =
      P * W := by
      have hP :
        P =
          (List.ofFn fun i : Fin m =>
            swapMatrix (α := α) (Fin.castLE hmn i.castSucc) (d i.castSucc)).prod := by
        dsimp only [P, d']
        refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
        rw [hcast]
      rw [ofFn_snoc (fun i => swapMatrix (α := α) (Fin.castLE hmn i) (d i)),
        List.prod_append, List.prod_singleton, hP]
    rw [hfold, hL, ← vecMul_vecMul,
      GetDot_SwapMatrix.eq.Get
        (x ᵥ* P) (Fin.castLE hmn (Fin.last m)) (d (Fin.last m))]
    funext k
    rw [Equiv.Perm.mul_apply]
    simp only [Function.comp_apply]
    apply congrFun (ih hmn' d')


-- created on 2026-10-31
