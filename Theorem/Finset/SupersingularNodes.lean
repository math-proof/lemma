module

public import Theorem.Finsupp.SpecializeModuli

public noncomputable section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable {K : Type*} [Field K]


@[simp] public theorem frobNodePair_fst (q : ℕ) (a : K) :
    (frobNodePair q a).1 = charLGeomPlaceOfPoint K a := rfl


@[simp] public theorem frobNodePair_snd (q : ℕ) (a : K) :
    (frobNodePair q a).2 = charLGeomPlaceOfPoint K (a ^ q) := rfl


public theorem frobNodePair_injective (q : ℕ) : Function.Injective (frobNodePair (K := K) q) :=
  fun _ _ h => charLGeomPlaceOfPoint_injective K (congrArg Prod.fst h)


@[simp] public theorem frobNodePairEmb_apply (q : ℕ) (a : K) :
    frobNodePairEmb q a = frobNodePair q a := rfl


public theorem mem_nodePairsOf_iff (q : ℕ) (S : Finset K)
    (s : Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1)) :
    s ∈ nodePairsOf q S ↔ ∃ a ∈ S, frobNodePair q a = s := by
  simp only [nodePairsOf, Finset.mem_map, frobNodePairEmb_apply]


public theorem frobNodePair_mem_nodePairsOf (q : ℕ) {S : Finset K} {a : K} (ha : a ∈ S) :
    frobNodePair q a ∈ nodePairsOf q S :=
  Finset.mem_map_of_mem (frobNodePairEmb q) ha


@[simp] public theorem card_nodePairsOf (q : ℕ) (S : Finset K) : (nodePairsOf q S).card = S.card :=
  Finset.card_map _


public theorem jOfNode_mem (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) : jOfNode q S s ∈ S :=
  (Classical.choose_spec ((mem_nodePairsOf_iff q S s).mp s.2)).1


@[simp] public theorem frobNodePair_jOfNode (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) :
    frobNodePair q (jOfNode q S s) = s :=
  (Classical.choose_spec ((mem_nodePairsOf_iff q S s).mp s.2)).2


@[simp] public theorem jOfNode_mk (q : ℕ) {S : Finset K} {a : K} (ha : a ∈ S) :
    jOfNode q S ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q ha⟩ = a :=
  frobNodePair_injective q (frobNodePair_jOfNode q S _)


public theorem jOfNode_injective (q : ℕ) (S : Finset K) : Function.Injective (jOfNode q S) :=
  fun s t h => Subtype.ext (by rw [← frobNodePair_jOfNode q S s, ← frobNodePair_jOfNode q S t, h])


@[simp] public theorem coe_nodeEquiv_apply (q : ℕ) (S : Finset K) (a : ↥S) :
    ((nodeEquiv q S a : ↥(nodePairsOf q S)) :
      Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1))
      = frobNodePair q (a : K) := rfl


@[simp] public theorem coe_nodeEquiv_symm_apply (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) :
    ((nodeEquiv q S).symm s : K) = jOfNode q S s := rfl


public theorem widthOf_apply (q : ℕ) (S : Finset K) (e : K → ℕ) (s : ↥(nodePairsOf q S)) :
    widthOf q S e s = e (jOfNode q S s) := rfl


@[simp] public theorem widthOf_mk (q : ℕ) {S : Finset K} (e : K → ℕ) {a : K} (ha : a ∈ S) :
    widthOf q S e ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q ha⟩ = e a := by
  rw [widthOf_apply, jOfNode_mk q ha]


public theorem widthOf_nodeEquiv (q : ℕ) (S : Finset K) (e : K → ℕ) (a : ↥S) :
    widthOf q S e (nodeEquiv q S a) = e a :=
  widthOf_mk q e a.2

end ModularCurve

end
