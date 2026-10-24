/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean -/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import sympy.atlas.Combinatorics.InfiniteWord.MorphicWord
import Lemma.Finset.InfiniteWord.MorphicWord
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.Logic.Function.CompTypeclasses

/-!
# Cobham: `k`-automatic sequences are codings of prolongable `k`-uniform fixed points

The one-base characterization (stable ID
`jis_grounded_7ab6fb1531d4463cd12a1a80`). This is not the distinct two-base
periodicity theorem.

Provenance: Sunic, JIS VOL10,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Sunic/cubefree.tex>,
file SHA-256
`ef2bc04940dde383128c102334a4c332443a2124706971b1bcf3b50bd2fd5c9b`;
Stipulanti, JIS VOL21,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Stipulanti/stip8.tex>,
file SHA-256
`a535e42b1e5cfcbd668a44b952035dd8b647208ec35ddf93dfa245c04b1528c2`.
-/

section
namespace MetaMathlibExt

/-- Least-significant-digit-first value of a base-`k` digit word.

Sunic selects least-significant-digit reading with tolerance of trailing
high-order zeros: lines 562-567 of `cubefree.tex`, span SHA-256
`e7c8c89ab0663ef3fe4e59fcb7a16bcf952104852337ffbdab1ed42fc6c20921`. -/
def baseWordValueLSD {k : Nat} (ds : List (Fin k)) : Nat :=
  ds.foldr (fun d acc => d.val + k * acc) 0

/-- A sequence is `k`-automatic when a finite output automaton computes each
term from every base-`k` expansion of its index.

Sunic Definition 3, lines 556-560 of `cubefree.tex`, span SHA-256
`fd6739cecadd7bfc1b66a49c39db59b2a267e85abb0abf5556bac6b533f3330b`.
The universal clause over all representing words enforces tolerance of
trailing high-order zeros. -/
def IsKAutomaticSequence {B : Type} [Fintype B] (k : Nat) (w : Nat → B) : Prop :=
  2 ≤ k ∧
    ∃ q : Nat, 0 < q ∧
      ∃ start : Fin q,
        ∃ trans : Fin q → Fin k → Fin q,
          ∃ out : Fin q → B,
            ∀ n : Nat, ∀ ds : List (Fin k),
              baseWordValueLSD ds = n → out (ds.foldl trans start) = w n

/-- A sequence is a coding of a prolongable `k`-uniform fixed point: all
letter images have length `k`, the start letter's image begins with itself,
`u` satisfies the block law, and `g` codes `u` to `w` pointwise.

Sunic lines 569-584 state the equivalence and define prolongability and
uniformity (`cubefree.tex`, span SHA-256
`f618b2151d7a9680b94b6865bd471b1375fb23b387579b274c1e3174b9591763`);
Stipulanti lines 164-174 define morphism, coding, prolongability, and fixed
point (`stip8.tex`, span SHA-256
`cbafa712ca06a7c28b1c8cd9f5d425c3b6fc518d168a321d79aed28293c2d651`). -/
def IsCodingOfProlongableKUniformFixedPoint {B : Type} [Fintype B] (k : Nat)
    (w : Nat → B) : Prop :=
  2 ≤ k ∧
    ∃ q : Nat, 0 < q ∧
      ∃ f : Fin q → List (Fin q), (∀ a : Fin q, (f a).length = k) ∧
        ∃ a : Fin q, ∃ tl : List (Fin q), tl ≠ [] ∧ f a = a :: tl ∧
          ∃ u : Nat → Fin q, u 0 = a ∧
            (∀ n : Nat, ∀ j : Nat, j < k → (f (u n)).getD j a = u (k * n + j)) ∧
              ∃ g : Fin q → B, ∀ n : Nat, w n = g (u n)

/-- Canonical least-significant-digit-first expansion of `n` in base `k`. -/
private def repList {k : Nat} (hk : 2 ≤ k) : Nat → List (Fin k)
  | 0 => []
  | n + 1 => ⟨(n + 1) % k, Nat.mod_lt _ (by omega)⟩ :: repList hk ((n + 1) / k)
termination_by n => n
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (by omega)

/-- Composition of block maps along a digit word (least significant first). -/
private def morphComp {q k : Nat} (f : Fin q → List (Fin q)) (a : Fin q)
    (ds : List (Fin k)) : Fin q → Fin q :=
  ds.foldr (fun d F => (fun s => (f s).getD d.val a) ∘ F) id

/-- Automaton transition on function states for the backward direction. -/
private def autoTrans {q k q' : Nat} (f : Fin q → List (Fin q)) (a : Fin q)
    (e : (Fin q → Fin q) ≃ Fin q') : Fin q' → Fin k → Fin q' :=
  fun G d => e ((e.symm G) ∘ (fun s => (f s).getD d.val a))

/-- Run an automaton from a given state along a digit word. -/
private def runFrom {q k : Nat} (trans : Fin q → Fin k → Fin q) (s : Fin q)
    (ds : List (Fin k)) : Fin q :=
  ds.foldl trans s

/-- Block map of a single digit. -/
private def transFn {q k : Nat} (trans : Fin q → Fin k → Fin q) (d : Fin k) :
    Fin q → Fin q :=
  fun s => trans s d

/-- Image of a function-state under one digit; `Option.none` is the fresh start. -/
private def imgAbove {q k : Nat} (trans : Fin q → Fin k → Fin q)
    (G : Option (Fin q → Fin q)) (d : Fin k) : Option (Fin q → Fin q) :=
  match G with
  | Option.none => if d.val = 0 then Option.none else Option.some (transFn trans d)
  | Option.some F => Option.some (F ∘ transFn trans d)

/-- Morphism on coded states: `k` images, one per digit. -/
private def morphImg {q k q' : Nat} (trans : Fin q → Fin k → Fin q)
    (e : Option (Fin q → Fin q) ≃ Fin q') : Fin q' → List (Fin q') :=
  fun G => List.ofFn (fun d : Fin k => e (imgAbove trans (e.symm G) d))

/-- Fixed point: fresh start at `0`, runs of canonical expansions elsewhere. -/
private def morphFix {q k q' : Nat} (trans : Fin q → Fin k → Fin q) (hk : 2 ≤ k)
    (e : Option (Fin q → Fin q) ≃ Fin q') : Nat → Fin q' :=
  fun n => e (if n = 0 then Option.none
    else Option.some (fun s => runFrom trans s (repList hk n)))
end MetaMathlibExt
