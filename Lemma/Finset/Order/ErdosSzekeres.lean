import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Order.ErdosSzekeres
open MathlibExt.Combinatorics.Order.ErdosSzekeres


/--
[sub_one_lt_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma sub_one_lt_of_pos_eq
  {k : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  k - 1 < k := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.sub_one_lt_of_pos hk

/--
[fin1_false](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma fin1_false_eq
  {i j : Fin 1}
-- given
  (hij : i < j) :
-- imply
  False := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.fin1_false hij

/--
[singleton_incr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma singleton_incr_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  IsIncrSubseq f 1 (fun _ => p) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.singleton_incr f p

/--
[singleton_decr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma singleton_decr_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  IsDecrSubseq f 1 (fun _ => p) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.singleton_decr f p

/--
[subseqLen_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma subseqLen_le_eq
  {N k : ℕ}
  {φ : Fin k → Fin N}
-- given
  (hidx : ∀ i j : Fin k, i < j → φ i < φ j) :
-- imply
  k ≤ N := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.subseqLen_le hidx

/--
[incrLen_isEnd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma incrLen_isEnd_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  IsIncrEnd f p (incrLen f p) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.incrLen_isEnd f p

/--
[decrLen_isEnd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma decrLen_isEnd_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  IsDecrEnd f p (decrLen f p) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.decrLen_isEnd f p

/--
[le_incrLen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma le_incrLen_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N}
  {k : ℕ}
-- given
  (h : IsIncrEnd f p k) :
-- imply
  k ≤ incrLen f p := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.le_incrLen f p k h

/--
[le_decrLen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma le_decrLen_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N}
  {k : ℕ}
-- given
  (h : IsDecrEnd f p k) :
-- imply
  k ≤ decrLen f p := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.le_decrLen f p k h

/--
[incrLen_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma incrLen_ge_one_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  1 ≤ incrLen f p := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.incrLen_ge_one f p

/--
[decrLen_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma decrLen_ge_one_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {p : Fin N} :
-- imply
  1 ≤ decrLen f p := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.decrLen_ge_one f p

/--
[idx_le_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma idx_le_last_eq
  {N k : ℕ}
  {q : Fin N}
  {φ : Fin k → Fin N}
  {i : Fin (k + 1)}
-- given
  (hk : 0 < k)
  (hidx : ∀ i j : Fin k, i < j → φ i < φ j)
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hik : i.val < k) :
-- imply
  φ ⟨i.val, hik⟩ ≤ q := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.idx_le_last hk hidx hlast hik

/--
[val_le_last_incr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma val_le_last_incr_eq
  {N k : ℕ}
  {f : Fin N → ℝ}
  {q : Fin N}
  {φ : Fin k → Fin N}
  {i : Fin (k + 1)}
-- given
  (hk : 0 < k)
  (hval : ∀ i j : Fin k, i < j → f (φ i) < f (φ j))
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hik : i.val < k) :
-- imply
  f (φ ⟨i.val, hik⟩) ≤ f q := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.val_le_last_incr hk hval hlast hik

/--
[last_le_val_decr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma last_le_val_decr_eq
  {N k : ℕ}
  {f : Fin N → ℝ}
  {q : Fin N}
  {φ : Fin k → Fin N}
  {i : Fin (k + 1)}
-- given
  (hk : 0 < k)
  (hval : ∀ i j : Fin k, i < j → f (φ j) < f (φ i))
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hik : i.val < k) :
-- imply
  f q ≤ f (φ ⟨i.val, hik⟩) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.last_le_val_decr hk hval hlast hik

/--
[extend_idx](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma extend_idx_eq
  {N k : ℕ}
  {q p : Fin N}
  {φ : Fin k → Fin N}
  {i j : Fin (k + 1)}
-- given
  (hk : 0 < k)
  (hidx : ∀ i j : Fin k, i < j → φ i < φ j)
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hqp : q < p)
  (hij : i < j) :
-- imply
  extendMap φ p i < extendMap φ p j := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.extend_idx hk hidx hlast hqp i j hij

/--
[extend_last](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma extend_last_eq
  {N k : ℕ}
  {φ : Fin k → Fin N}
  {p : Fin N}
-- given
  (hk1 : 0 < k + 1) :
-- imply
  extendMap φ p ⟨k + 1 - 1, sub_one_lt_of_pos hk1⟩ = p := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.extend_last φ hk1

/--
[incrExtend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma incrExtend_eq
  {N k : ℕ}
  {f : Fin N → ℝ}
  {q p : Fin N}
  {φ : Fin k → Fin N}
-- given
  (hk : 0 < k)
  (hsub : IsIncrSubseq f k φ)
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hqp : q < p)
  (hval : f q < f p) :
-- imply
  IsIncrEnd f p (k + 1) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.incrExtend hk hsub hlast hqp hval

/--
[decrExtend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma decrExtend_eq
  {N k : ℕ}
  {f : Fin N → ℝ}
  {q p : Fin N}
  {φ : Fin k → Fin N}
-- given
  (hk : 0 < k)
  (hsub : IsDecrSubseq f k φ)
  (hlast : φ ⟨k - 1, sub_one_lt_of_pos hk⟩ = q)
  (hqp : q < p)
  (hval : f p < f q) :
-- imply
  IsDecrEnd f p (k + 1) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.decrExtend hk hsub hlast hqp hval

/--
[incrMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma incrMono_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {q p : Fin N}
-- given
  (hqp : q < p)
  (hval : f q < f p) :
-- imply
  incrLen f q < incrLen f p := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.incrMono f hqp hval

/--
[decrMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma decrMono_eq
  {N : ℕ}
  {f : Fin N → ℝ}
  {q p : Fin N}
-- given
  (hqp : q < p)
  (hval : f p < f q) :
-- imply
  decrLen f q < decrLen f p := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.decrMono f hqp hval

/--
[truncIncr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma truncIncr_eq
  {N k r : ℕ}
  {f : Fin N → ℝ}
  {φ : Fin k → Fin N}
-- given
  (hsub : IsIncrSubseq f k φ)
  (hrk : r ≤ k) :
-- imply
  ∃ φ' : Fin r → Fin N, IsIncrSubseq f r φ' := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.truncIncr hsub hrk

/--
[truncDecr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma truncDecr_eq
  {N k s : ℕ}
  {f : Fin N → ℝ}
  {φ : Fin k → Fin N}
-- given
  (hsub : IsDecrSubseq f k φ)
  (hsk : s ≤ k) :
-- imply
  ∃ ψ : Fin s → Fin N, IsDecrSubseq f s ψ := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.truncDecr hsub hsk

/--
[erdos_szekeres](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean)
-/
@[path]
private lemma erdos_szekeres_eq
  {r s : ℕ}
  {f : Fin ((r - 1) * (s - 1) + 1) → ℝ}
-- given
  (hr : 0 < r)
  (hs : 0 < s)
  (hinj : Function.Injective f) :
-- imply
  (∃ φ : Fin r → Fin ((r - 1) * (s - 1) + 1),
    (∀ i j : Fin r, i < j → φ i < φ j) ∧
    (∀ i j : Fin r, i < j → f (φ i) < f (φ j))) ∨
    (∃ ψ : Fin s → Fin ((r - 1) * (s - 1) + 1),
    (∀ i j : Fin s, i < j → ψ i < ψ j) ∧
    (∀ i j : Fin s, i < j → f (ψ j) < f (ψ i))) := by
-- proof
  apply MathlibExt.Combinatorics.Order.ErdosSzekeres.erdos_szekeres hr hs f hinj


-- created on 2026-10-20
