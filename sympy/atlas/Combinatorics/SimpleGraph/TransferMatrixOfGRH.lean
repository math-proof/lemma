/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/TransferMatrixOfGRH.lean -/

import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Transfer matrices for relational graph sums

This file formalizes the transfer-matrix definition of Bautista-Ramos and
Guillén-Galván, *Fibonacci Numbers of Generalized Zykov Sums*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Bautista/bautista4.tex>.

The source permits graphs with loops and notes that a loop prevents its vertex
from belonging to an independent set. Mathlib's `SimpleGraph` is irreflexive,
so the API below intentionally covers only the loopless specialization of the
source construction. It makes no claim about the source's looped-graph case.
-/

open scoped BigOperators

namespace MetaMathlibExt

/-- The Boolean zero indicator used in the source's transfer matrix. -/
def zykovZeroIndicator (z : ℕ) : Bool :=
  decide (z = 0)

/-- The Boolean characteristic vector of a finite independent set in a
loopless `SimpleGraph`. -/
def independentSetCharacteristic {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    (A : {s : Finset V // G.IsIndepSet (↑s : Set V)}) : V → Bool :=
  fun v => decide (v ∈ A.val)

/-- The natural-valued pairing of two Boolean vectors along a relation `R`. -/
def relationPairing {V W : Type*} [Fintype V] [Fintype W]
    (R : V → W → Prop) [∀ v w, Decidable (R v w)]
    (a : V → Bool) (b : W → Bool) : ℕ :=
  ∑ v : V, ∑ w : W, if R v w then if a v && b w then 1 else 0 else 0

/-- The transfer matrix of the relational graph sum `G +_R H`, represented as
its Boolean-valued entry function on pairs of independent sets. This is the
loopless specialization: both inputs are irreflexive Mathlib `SimpleGraph`s,
whereas the cited source also allows loops. -/
def zykovTransferMatrix {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (R : V → W → Prop) [∀ v w, Decidable (R v w)]
    (p : {s : Finset V // G.IsIndepSet (↑s : Set V)} ×
      {t : Finset W // H.IsIndepSet (↑t : Set W)}) : Bool :=
  zykovZeroIndicator
    (relationPairing R (independentSetCharacteristic G p.1) (independentSetCharacteristic H p.2))

end MetaMathlibExt
