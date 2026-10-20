import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.WorpitzkyMultisetIdentity
open MetaMathlibExt


/--
[worpitzky_identity_multiset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean)
-/
@[path]
private lemma worpitzky_identity_multiset_eq
  {m : ℕ}
  {k : Fin m → ℕ}
  {x : ℕ} :
-- imply
  Finset.prod Finset.univ (fun i => Nat.choose (x + k i - 1) (k i)) =
    Finset.sum (Finset.Icc 1 (max 1 (Finset.sum Finset.univ (fun a => k a)))) (fun p =>
    Nat.choose (x + Finset.sum Finset.univ (fun a => k a) - p)
    (Finset.sum Finset.univ (fun a => k a)) *
    Nat.card { w : Fin (Finset.sum Finset.univ (fun a => k a)) → Fin m //
    (∀ i,
    Fintype.card
    { j : Fin (Finset.sum Finset.univ (fun a => k a)) // w j = i } = k i) ∧
    (Finset.univ.filter
    (fun j : Fin (Finset.sum Finset.univ (fun a => k a)) =>
    ∃ h : j.val + 1 < Finset.sum Finset.univ (fun a => k a),
    w j > w ⟨j.val + 1, h⟩)).card + 1 = p }) := by
-- proof
  apply MetaMathlibExt.worpitzky_identity_multiset m k x


-- created on 2026-10-20
