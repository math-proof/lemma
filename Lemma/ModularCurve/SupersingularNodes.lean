import Lemma.ModularCurve.SpecializeModuli

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable {K : Type*} [Field K]

def frobNodePair (q : ℕ) (a : K) :
    Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1) :=
  (charLGeomPlaceOfPoint K a, charLGeomPlaceOfPoint K (a ^ q))

@[simp] theorem frobNodePair_fst (q : ℕ) (a : K) :
    (frobNodePair q a).1 = charLGeomPlaceOfPoint K a := rfl

@[simp] theorem frobNodePair_snd (q : ℕ) (a : K) :
    (frobNodePair q a).2 = charLGeomPlaceOfPoint K (a ^ q) := rfl

theorem frobNodePair_injective (q : ℕ) : Function.Injective (frobNodePair (K := K) q) :=
  fun _ _ h => charLGeomPlaceOfPoint_injective K (congrArg Prod.fst h)

def frobNodePairEmb (q : ℕ) :
    K ↪ Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1) :=
  ⟨frobNodePair q, frobNodePair_injective q⟩

@[simp] theorem frobNodePairEmb_apply (q : ℕ) (a : K) :
    frobNodePairEmb q a = frobNodePair q a := rfl

def nodePairsOf (q : ℕ) (S : Finset K) :
    Finset (Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1)) :=
  S.map (frobNodePairEmb q)

theorem mem_nodePairsOf_iff (q : ℕ) (S : Finset K)
    (s : Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1)) :
    s ∈ nodePairsOf q S ↔ ∃ a ∈ S, frobNodePair q a = s := by
  simp only [nodePairsOf, Finset.mem_map, frobNodePairEmb_apply]

theorem frobNodePair_mem_nodePairsOf (q : ℕ) {S : Finset K} {a : K} (ha : a ∈ S) :
    frobNodePair q a ∈ nodePairsOf q S :=
  Finset.mem_map_of_mem (frobNodePairEmb q) ha

@[simp] theorem card_nodePairsOf (q : ℕ) (S : Finset K) : (nodePairsOf q S).card = S.card :=
  Finset.card_map _

def jOfNode (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) : K :=
  Classical.choose ((mem_nodePairsOf_iff q S s).mp s.2)

theorem jOfNode_mem (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) : jOfNode q S s ∈ S :=
  (Classical.choose_spec ((mem_nodePairsOf_iff q S s).mp s.2)).1

@[simp] theorem frobNodePair_jOfNode (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) :
    frobNodePair q (jOfNode q S s) = s :=
  (Classical.choose_spec ((mem_nodePairsOf_iff q S s).mp s.2)).2

@[simp] theorem jOfNode_mk (q : ℕ) {S : Finset K} {a : K} (ha : a ∈ S) :
    jOfNode q S ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q ha⟩ = a :=
  frobNodePair_injective q (frobNodePair_jOfNode q S _)

theorem jOfNode_injective (q : ℕ) (S : Finset K) : Function.Injective (jOfNode q S) :=
  fun s t h => Subtype.ext (by rw [← frobNodePair_jOfNode q S s, ← frobNodePair_jOfNode q S t, h])

def nodeEquiv (q : ℕ) (S : Finset K) : ↥S ≃ ↥(nodePairsOf q S) where
  toFun a := ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q a.2⟩
  invFun s := ⟨jOfNode q S s, jOfNode_mem q S s⟩
  left_inv a := Subtype.ext (jOfNode_mk q a.2)
  right_inv s := Subtype.ext (frobNodePair_jOfNode q S s)

@[simp] theorem coe_nodeEquiv_apply (q : ℕ) (S : Finset K) (a : ↥S) :
    ((nodeEquiv q S a : ↥(nodePairsOf q S)) :
      Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1))
      = frobNodePair q (a : K) := rfl

@[simp] theorem coe_nodeEquiv_symm_apply (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) :
    ((nodeEquiv q S).symm s : K) = jOfNode q S s := rfl

def widthOf (q : ℕ) (S : Finset K) (e : K → ℕ) : ↥(nodePairsOf q S) → ℕ :=
  fun s => e (jOfNode q S s)

theorem widthOf_apply (q : ℕ) (S : Finset K) (e : K → ℕ) (s : ↥(nodePairsOf q S)) :
    widthOf q S e s = e (jOfNode q S s) := rfl

@[simp] theorem widthOf_mk (q : ℕ) {S : Finset K} (e : K → ℕ) {a : K} (ha : a ∈ S) :
    widthOf q S e ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q ha⟩ = e a := by
  rw [widthOf_apply, jOfNode_mk q ha]

theorem widthOf_nodeEquiv (q : ℕ) (S : Finset K) (e : K → ℕ) (a : ↥S) :
    widthOf q S e (nodeEquiv q S a) = e a :=
  widthOf_mk q e a.2

end ModularCurve

end
