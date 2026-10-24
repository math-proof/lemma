/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GaussianQBinomial.lean -/

import Mathlib.Algebra.Polynomial.Basic

namespace MetaMathlibExt

open Finset

private def partner (n : ℕ) (j : Fin n) : Fin n :=
  if _h : j.val % 2 = 0 then
    if _h2 : j.val + 1 < n then ⟨j.val + 1, _h2⟩ else j
  else ⟨j.val - 1, by have hj := j.isLt; omega⟩

private def bstart (n : ℕ) (j : Fin n) : Fin n :=
  if _h : j.val % 2 = 0 then j else ⟨j.val - 1, by have hj := j.isLt; omega⟩

private def sigmaPos (n : ℕ) (T : Finset (Fin n)) (j : Fin n) : Fin n :=
  if bstart n j ∈ T then partner n j else j

private def psb (n : ℕ) (w : Fin n → Fin 2) : Bool :=
  decide (∀ j j' : Fin n, j.val % 2 = 0 → j'.val = j.val + 1 → w j ≤ w j')

private def ascSet (n : ℕ) (w : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter
    (fun j => j.val % 2 = 0 ∧ ∃ j' : Fin n, j'.val = j.val + 1 ∧ w j < w j')

private def descSet (n : ℕ) (w : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter
    (fun j => j.val % 2 = 0 ∧ ∃ j' : Fin n, j'.val = j.val + 1 ∧ w j' < w j)

private def invSet (n : ℕ) (w : Fin n → Fin 2) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ w p.1 > w p.2)

private def wordsSet (n k : ℕ) : Finset (Fin n → Fin 2) :=
  Finset.univ.filter
    (fun v => (Finset.univ.filter (fun i : Fin n => v i = (1 : Fin 2))).card = k)

private def flip (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i => w (sigmaPos n T i)

private def newSet (n : ℕ) (T : Finset (Fin n)) (w : Fin n → Fin 2) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter
    (fun p => sigmaPos n T p.1 < sigmaPos n T p.2 ∧ w p.1 > w p.2)

private def extraSet (n : ℕ) (T : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  T.image (fun j => (partner n j, j))
end MetaMathlibExt
