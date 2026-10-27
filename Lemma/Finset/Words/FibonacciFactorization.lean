import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Words.FibonacciFactorization
open MetaMathlibExt


namespace MetaMathlibExt

/--
[fibWord_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
lemma fibWord_add_two
  {n : ℕ} :
-- imply
  fibWord (n + 2) = fibWord (n + 1) ++ fibWord n := by
-- proof
  induction n with
  | zero => rfl
  | succ n ih =>
    change fibMorph (fibWord (n + 2)) = fibMorph (fibWord (n + 1)) ++ fibMorph (fibWord n)
    rw [ih, fibMorph_append]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibWord_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
lemma fibWord_factorization
  {N : ℕ} :
-- imply
  false :: true :: (List.range N).flatMap fibWord = fibWord (N + 1) := by
-- proof
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.cons_append,
      ← List.cons_append, ih, fibWord_add_two]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibWord_eq_ofFn_fibInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
lemma fibWord_eq_ofFn_fibInf
  {n : ℕ} :
-- imply
  fibWord n = List.ofFn (fun i : Fin (fibWord n).length => fibInf i) := by
-- proof
  refine List.ext_getElem (by simp) fun i h _ => ?_
  rw [List.getElem_ofFn, ← fibInf_agrees n i h]
  simp [h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ofFn_prefix_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
private lemma ofFn_prefix_of_le {α : Type*} (g : ℕ → α) {k m : ℕ} (hkm : k ≤ m) :
  List.ofFn (fun i : Fin k => g i) <+: List.ofFn (fun i : Fin m => g i) := by
  rw [List.prefix_iff_getElem]
  exact ⟨by simpa using hkm, fun i hi => by simp⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibInf_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
lemma fibInf_factorization
  :
-- imply
  (∀ N : ℕ,
    let w := by
-- proof
  refine ⟨fun N => ?_, fun k => ⟨k, ?_⟩⟩
  · change false :: true :: (List.range N).flatMap fibWord = List.ofFn
    (fun i : Fin (false :: true :: (List.range N).flatMap fibWord).length => fibInf i)
    rw [fibWord_factorization]
    exact fibWord_eq_ofFn_fibInf (N + 1)
  · rw [fibWord_factorization, fibWord_eq_ofFn_fibInf (k + 1)]
    have := fibWord_length (k + 1)
    exact ofFn_prefix_of_le fibInf (by omega)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibonacci_infinite_word_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
lemma fibonacci_infinite_word_factorization
  {f : ℕ → Fin 2}
  {fibWord : ℕ → List (Fin 2)}
-- given
  (h_one : fibWord 1 = [1])
  (h_two : fibWord 2 = [0])
  (h_rec : ∀ n : ℕ, fibWord (n + 3) = fibWord (n + 2) ++ fibWord (n + 1))
  (h_limit : ∀ n : ℕ, fibWord (n + 2) = List.ofFn (fun i : Fin (fibWord (n + 2)).length => f i)) :
-- imply
  (∀ N : ℕ,
    let w := by
-- proof
  have heq : ∀ N : ℕ,
    (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))) = fibWord (N + 2) :=
    fibWord_concat_eq fibWord h_one h_two h_rec
  refine ⟨?_, fun k => ⟨k, ?_⟩⟩
  · intro N
    change (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))) =
      List.ofFn (fun i : Fin (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))).length => f i)
    rw [heq N]
    exact h_limit N
  · have hlen : k ≤ (fibWord (k + 2)).length := by
    rw [fibWord_bridge fibWord h_one h_two h_rec k, List.length_map]
    have := fibWord_length k
    omega
    rw [heq k, h_limit k]
    exact ofFn_prefix_of_le f hlen

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
