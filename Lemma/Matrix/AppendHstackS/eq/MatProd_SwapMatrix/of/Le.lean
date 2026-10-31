import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic
import Lemma.Matrix.AppendHstackS.eq.SwapMatrix
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
  (hm : m ≤ n)
  (b : Fin m → Fin n) :
-- imply
  (fromBlocks
    ((List.ofFn fun i : Fin m => swapMatrix (α := α) (Fin.castLE hm i) (b i)).prod)
    0 0 (1 : Matrix (Fin 1) (Fin 1) α)).reindex finSumFinEquiv finSumFinEquiv =
  (List.ofFn fun i : Fin m =>
    swapMatrix (α := α)
      (Fin.castAdd 1 (Fin.castLE hm i))
      (Fin.castAdd 1 (b i))).prod := by
-- proof
  induction m with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    rw [fromBlocks_one, reindex_apply, submatrix_one_equiv]
  | succ m ih =>
    let b' : Fin m → Fin n := fun i => b i.castSucc
    let hm' : m ≤ n := Nat.le_of_succ_le hm
    let P : Matrix (Fin n) (Fin n) α :=
      (List.ofFn fun i : Fin m =>
        swapMatrix (α := α) (Fin.castLE hm i.castSucc) (b i.castSucc)).prod
    let W : Matrix (Fin n) (Fin n) α :=
      swapMatrix (α := α) (Fin.castLE hm (Fin.last m)) (b (Fin.last m))
    let P' : Matrix (Fin (n + 1)) (Fin (n + 1)) α :=
      (List.ofFn fun i : Fin m =>
        swapMatrix (α := α)
          (Fin.castAdd 1 (Fin.castLE hm i.castSucc))
          (Fin.castAdd 1 (b i.castSucc))).prod
    let W' : Matrix (Fin (n + 1)) (Fin (n + 1)) α :=
      swapMatrix (α := α)
        (Fin.castAdd 1 (Fin.castLE hm (Fin.last m)))
        (Fin.castAdd 1 (b (Fin.last m)))
    have hL :
      (List.ofFn fun i : Fin (m + 1) =>
        swapMatrix (α := α) (Fin.castLE hm i) (b i)).prod =
      P * W := by
      rw [ofFn_snoc (fun i => swapMatrix (α := α) (Fin.castLE hm i) (b i)),
        List.prod_append, List.prod_singleton]
    have hR :
      (List.ofFn fun i : Fin (m + 1) =>
        swapMatrix (α := α)
          (Fin.castAdd 1 (Fin.castLE hm i))
          (Fin.castAdd 1 (b i))).prod =
      P' * W' := by
      rw [ofFn_snoc
        (fun i =>
          swapMatrix (α := α)
            (Fin.castAdd 1 (Fin.castLE hm i))
            (Fin.castAdd 1 (b i))),
        List.prod_append, List.prod_singleton]
    have hblock :
      fromBlocks (P * W) 0 0 (1 : Matrix (Fin 1) (Fin 1) α) =
        fromBlocks P 0 0 1 * fromBlocks W 0 0 1 := by
      rw [fromBlocks_multiply]
      simp
    have hcast (i : Fin m) :
      Fin.castLE hm i.castSucc = Fin.castLE hm' i := by
      ext
      simp
    have hP :
      P =
        (List.ofFn fun i : Fin m =>
          swapMatrix (α := α) (Fin.castLE hm' i) (b' i)).prod := by
      dsimp only [P, b']
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
      rw [hcast]
    have hP' :
      P' =
        (List.ofFn fun i : Fin m =>
          swapMatrix (α := α)
            (Fin.castAdd 1 (Fin.castLE hm' i))
            (Fin.castAdd 1 (b' i))).prod := by
      dsimp only [P', b']
      refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
      rw [hcast]
    rw [hL, hR, hblock]
    rw [← coe_reindexRingEquiv (R := α) finSumFinEquiv]
    rw [RingEquiv.map_mul]
    rw [coe_reindexRingEquiv]
    congr 1
    ·
      rw [hP, hP']
      exact ih hm' b'
    ·
      exact AppendHstackS.eq.SwapMatrix
        (i := Fin.castLE hm (Fin.last m)) (j := b (Fin.last m))


-- created on 2026-10-31
