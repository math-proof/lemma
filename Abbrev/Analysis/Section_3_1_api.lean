module

public import Instance.Analysis.Section_3_1_order
public import Theorem.Set.Eq.of.Object
public import Theorem.Set.Object.is.Eq
public import Theorem.Set.Eq.of.All_In
public import Theorem.Set.All_Empty
public import Theorem.Set.Any_In.of.Ne_Empty
public import Theorem.Set.NeEmpty.of.In
public import Theorem.Set.In_Set.is.Eq
public import Theorem.Set.In_Union.is.InOrIn
public import Theorem.Set.In_Insert.is.EqOrIn
public import Theorem.Set.Set.eq.Union
public import Theorem.Set.In_Set.is.EqOrEq
public import Theorem.Set.In_Set.is.EqOrEqOrEq
public import Theorem.Set.Eq_UnionSet
public import Theorem.Set.EqUnionSet
public import Theorem.Set.IffSubsetAllIn
public import Theorem.Set.Iff_SubsetAndNe
public import Theorem.Set.InVal
public import Theorem.Set.EqVal
public import Theorem.Set.Val.is.Eq
public import Theorem.Set.EqSubtypeMk.of.In
public import Theorem.Set.In.of.In_Specify
public import Theorem.Set.IffVal.in.Specify
public import Theorem.Set.In_Specify.is.Any
public import Theorem.Set.In_Inter.is.InAndIn
public import Theorem.Set.IffIn
public import Theorem.Set.Disjoint.is.Inter.eq.Empty
public import Theorem.Set.In_Replace.is.Any.of.All_Eq
public import Theorem.Nat.Nat.eq.Object
public import Theorem.Nat.OfNat.eq.Object
public import Theorem.Nat.Object
public import Theorem.Nat.EqObject
public import Theorem.Nat.Nat.eq.OfNat
public import Theorem.Nat.Nat.is.Eq
public import Theorem.Nat.IffEqEq
public import Theorem.Nat.EqOfSNat
public import Theorem.Nat.IffOfSNat
public import Theorem.Nat.Object.eq.OfNat.is.Eq
public import Theorem.Nat.Object.is.Eq
public import Theorem.Nat.EqNat
public import Theorem.Nat.Eq_Nat
public import Theorem.Nat.Eq_OfNat
public import Theorem.Nat.Object.eq.OfNat.is.Eq_OfNat
public import Theorem.Set.SetObject.is.Eq
public import Theorem.Set.In_SetObject.is.In

@[expose] public section


namespace Chapter3

universe u v

variable [SetTheory]

open SetTheory

open SetTheory.Set

abbrev SetTheory.Set.coe_eq {X Y:Set} (h: (X: Object) = (Y: Object)) : X = Y  :=
  _root_.Set.Eq.of.Object (X := X) (Y := Y) (h := h)

@[simp]
abbrev SetTheory.Set.coe_eq_iff (X Y:Set) : (X: Object) = (Y: Object) ↔  X = Y  :=
  _root_.Set.Object.is.Eq (X := X) (Y := Y)

@[ext]
abbrev SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y  :=
  _root_.Set.Eq.of.All_In (X := X) (Y := Y) (h := h)

@[simp]
abbrev SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set)  :=
  _root_.Set.All_Empty

abbrev SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X  :=
  _root_.Set.Any_In.of.Ne_Empty (X := X) (h := h)

abbrev SetTheory.Set.nonempty_of_inhabited {X:Set} {x:Object} (h:x ∈ X) : X ≠ ∅  :=
  _root_.Set.NeEmpty.of.In (X := X) (x := x) (h := h)

abbrev SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a  :=
  _root_.Set.In_Set.is.Eq (x := x) (a := a)

abbrev SetTheory.Set.mem_union (x:Object) (X Y:Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y)  :=
  _root_.Set.In_Union.is.InOrIn (x := x) (X := X) (Y := Y)

@[simp]
abbrev SetTheory.Set.mem_insert (a b: Object) (X: Set) : a ∈ insert b X ↔ a = b ∨ a ∈ X  :=
  _root_.Set.In_Insert.is.EqOrIn (a := a) (b := b) (X := X)

abbrev SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b}  :=
  _root_.Set.Set.eq.Union (a := a) (b := b)

@[simp]
abbrev SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b)  :=
  _root_.Set.In_Set.is.EqOrEq (x := x) (a := a) (b := b)

@[simp]
abbrev SetTheory.Set.mem_triple (x a b c:Object) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c)  :=
  _root_.Set.In_Set.is.EqOrEqOrEq (x := x) (a := a) (b := b) (c := c)

abbrev SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c}  :=
  _root_.Set.Eq_UnionSet (a := a) (b := b) (c := c)

abbrev SetTheory.Set.pair_union_pair (a b c:Object) :
    ({a,b}:Set) ∪ {b,c} = {a,b,c}  :=
  _root_.Set.EqUnionSet (a := a) (b := b) (c := c)

abbrev SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y  :=
  _root_.Set.IffSubsetAllIn (X := X) (Y := Y)

abbrev SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y)  :=
  _root_.Set.Iff_SubsetAndNe (X := X) (Y := Y)

abbrev SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A  :=
  _root_.Set.InVal (A := A) (x := x)

abbrev SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x  :=
  _root_.Set.EqVal (A := A) (x := x)

abbrev SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y  :=
  _root_.Set.Val.is.Eq (A := A) (x := x) (y := y)

@[simp]
abbrev SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x  :=
  _root_.Set.EqSubtypeMk.of.In (A := A) (x := x) (hx := hx)

abbrev SetTheory.Set.specification_axiom {A:Set} {P: A → Prop} {x:Object} (h: x ∈ A.specify P) :
    x ∈ A  :=
  _root_.Set.In.of.In_Specify (A := A) (P := P) (x := x) (h := h)

abbrev SetTheory.Set.specification_axiom' {A:Set} (P: A → Prop) (x:A) :
    x.val ∈ A.specify P ↔ P x  :=
  _root_.Set.IffVal.in.Specify (A := A) (x := x) (P := P)

@[simp]
abbrev SetTheory.Set.specification_axiom'' {A:Set} (P: A → Prop) (x:Object) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩  :=
  _root_.Set.In_Specify.is.Any (A := A) (x := x) (P := P)

abbrev SetTheory.Set.mem_inter (x:Object) (X Y:Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y)  :=
  _root_.Set.In_Inter.is.InAndIn (x := x) (X := X) (Y := Y)

abbrev SetTheory.Set.mem_sdiff (x:Object) (X Y:Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y)  :=
  _root_.Set.IffIn (x := x) (X := X) (Y := Y)

abbrev SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅  :=
  _root_.Set.Disjoint.is.Inter.eq.Empty (A := A) (B := B)

@[simp]
abbrev SetTheory.Set.replacement_axiom {A:Set} {P: A → Object → Prop}
  (hP: ∀ x y y', P x y ∧ P x y' → y = y') (y:Object) :
    y ∈ A.replace hP ↔ ∃ x, P x y  :=
  _root_.Set.In_Replace.is.Any.of.All_Eq (A := A) (P := P) (y := y) (hP := hP)

abbrev SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object)  :=
  _root_.Nat.Nat.eq.Object (n := n)

abbrev SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object)  :=
  _root_.Nat.OfNat.eq.Object (n := n)

@[simp]
abbrev SetTheory.Object.ofnat_eq'' {n:Nat} : ((n:ℕ):Object) = (n: Object)  :=
  _root_.Nat.Object (n := n)

@[simp]
abbrev SetTheory.Object.ofnat_eq''' {n:ℕ} {hn} : ((⟨(n:Object), hn⟩: nat): ℕ) = n  :=
  _root_.Nat.EqObject (n := n)

abbrev SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n  :=
  _root_.Nat.Nat.eq.OfNat (n := n)

@[simp]
abbrev SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m   :=
  _root_.Nat.Nat.is.Eq (n := n) (m := m)

@[simp]
abbrev SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m  :=
  _root_.Nat.IffEqEq (n := n) (m := m)

@[simp]
abbrev SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m)  :=
  _root_.Nat.EqOfSNat (n := n) (m := m)

abbrev SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m)  :=
  _root_.Nat.IffOfSNat (n := n) (m := m)

abbrev SetTheory.Set.nat_coe_eq_iff {m n : ℕ} : (m:Object) = ofNat(n) ↔ m = n  :=
  _root_.Nat.Object.eq.OfNat.is.Eq (m := m) (n := n)

abbrev SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m  :=
  _root_.Nat.Object.is.Eq (n := n) (m := m)

@[simp]
abbrev SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n  :=
  _root_.Nat.EqNat (n := n)

@[simp]
abbrev SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n  :=
  _root_.Nat.Eq_Nat (n := n)

@[simp]
abbrev SetTheory.Set.nat_equiv_coe_of_coe'' (n:ℕ) : ((ofNat(n):Nat):ℕ) = n  :=
  _root_.Nat.Eq_OfNat (n := n)

@[simp]
abbrev SetTheory.Set.nat_coe_eq_iff' {m: Nat} {n : ℕ} : (m:Object) = (ofNat(n):Object) ↔ (m:ℕ) = ofNat(n)  :=
  _root_.Nat.Object.eq.OfNat.is.Eq_OfNat (m := m) (n := n)

abbrev SetTheory.Set.coe_inj' (X Y:Set) :
    (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y  :=
  _root_.Set.SetObject.is.Eq (X := X) (Y := Y)

abbrev SetTheory.Set.mem_coe (X:Set) (x:Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X  :=
  _root_.Set.In_SetObject.is.In (X := X) (x := x)

end Chapter3
