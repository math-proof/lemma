module
public import Abbrev.Analysis.Section_3_3_fn
public import Abbrev.Analysis.Section_3_3_inv
public import Theorem.Set.EqToFn
public import Theorem.Set.EqIffP
public import Theorem.Set.EqGetMkFn
public import Theorem.Nat.P333a.Unique
public import Theorem.Nat.Eq_F333a.is.Eq_Add_1
public import Theorem.Nat.F333aNat.eq.Add_1
public import Theorem.Nat.F333a4.eq.Five
public import Theorem.Nat.F333a_AddMul2'3.eq.AddMul2'4
public import Theorem.Nat.NotP333b.Unique
public import Theorem.Set.P333c.Unique
public import Theorem.Set.Eq_F333c.is.EqAdd_1
public import Theorem.Nat.EqF333c_CoeNonzeroAdd_1
public import Theorem.Nat.F333c_CoeNonzero4.eq.Three
public import Theorem.Nat.F333c_CoeNonzeroAddMul2'3.eq.AddMul2'2
public import Theorem.Nat.P335.Unique
public import Theorem.Nat.F335.eq.Seven
public import Theorem.Set.Eq.is.All_Eq
public import Theorem.Nat.F3310a.eq.F3310b
public import Theorem.Set.Eq
public import Theorem.Set.ToFn.eq.ToFnToFn
public import Theorem.Nat.G3314F3314.eq.MkFn_AddMul2'3
public import Theorem.Nat.F3314G3314.eq.MkFn_AddMul2'6
public import Theorem.Set.Eq_SetTheory_Set_comp_assoc
public import Theorem.Set.OneToOne.is.All_Eq
public import Theorem.Set.OneToOne.is.InjectiveToFn
public import Theorem.Nat.OneToOneMkFn_Square
public import Theorem.Set.Any_And_Eq.of.NotOneToOne
public import Theorem.Set.Onto.is.SurjectiveToFn
public import Theorem.Set.Bijective.is.BijectiveToFn
public import Theorem.Set.Any_Any_And_NotBijective
public import Theorem.Set.Eq_GetInverse.is.Eq.of.Bijective
public import Theorem.Set.ToFnInverse.eq.InvFunToFn.of.Bijective


public section

namespace Chapter3

variable [SetTheory]

open SetTheory

open SetTheory.Set

open Function

abbrev Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x  :=
  _root_.Set.EqToFn (X := X) (Y := Y) (f := f) (x := x)

abbrev Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y  :=
  _root_.Set.EqIffP (X := X) (Y := Y) (f := f) (x := x) (y := y)

@[simp]
abbrev Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x  :=
  _root_.Set.EqGetMkFn (X := X) (Y := Y) (f := f) (x := x)

abbrev SetTheory.Set.P_3_3_3a_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_3a x y  :=
  _root_.Nat.P333a.Unique (x := x)

abbrev SetTheory.Set.f_3_3_3a_eval (x y: Nat) : y = f_3_3_3a x ↔ (y:ℕ) = (x+1:ℕ)  :=
  _root_.Nat.Eq_F333a.is.Eq_Add_1 (x := x) (y := y)

abbrev SetTheory.Set.f_3_3_3a_eval' (n: ℕ) : f_3_3_3a (n:Nat) = (n+1:ℕ)  :=
  _root_.Nat.F333aNat.eq.Add_1 (n := n)

abbrev SetTheory.Set.f_3_3_3a_eval'' : f_3_3_3a 4 = 5  :=
  _root_.Nat.F333a4.eq.Five

abbrev SetTheory.Set.f_3_3_3a_eval''' (n:ℕ) : f_3_3_3a (2*n+3: ℕ) = (2*n+4:ℕ)  :=
  _root_.Nat.F333a_AddMul2'3.eq.AddMul2'4 (n := n)

abbrev SetTheory.Set.not_P_3_3_3b_existsUnique : ¬ ∀ x, ∃! y: Nat, P_3_3_3b x y  :=
  _root_.Nat.NotP333b.Unique

abbrev SetTheory.Set.P_3_3_3c_existsUnique (x: (Nat \ {(0:Object)}: Set)) :
    ∃! y: Nat, P_3_3_3c x y  :=
  _root_.Set.P333c.Unique (x := x)

abbrev SetTheory.Set.f_3_3_3c_eval (x: (Nat \ {(0:Object)}: Set)) (y: Nat) :
    y = f_3_3_3c x ↔ ((y+1:ℕ):Object) = x  :=
  _root_.Set.Eq_F333c.is.EqAdd_1 (x := x) (y := y)

abbrev SetTheory.Set.f_3_3_3c_eval' (n: ℕ) : f_3_3_3c (coe_nonzero (n+1) (by positivity)) = n  :=
  _root_.Nat.EqF333c_CoeNonzeroAdd_1 (n := n)

abbrev SetTheory.Set.f_3_3_3c_eval'' : f_3_3_3c (coe_nonzero 4 (by positivity)) = 3  :=
  _root_.Nat.F333c_CoeNonzero4.eq.Three

abbrev SetTheory.Set.f_3_3_3c_eval''' (n:ℕ) :
    f_3_3_3c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ)  :=
  _root_.Nat.F333c_CoeNonzeroAddMul2'3.eq.AddMul2'2 (n := n)

abbrev SetTheory.Set.P_3_3_5_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_5 x y  :=
  _root_.Nat.P335.Unique (x := x)

abbrev SetTheory.Set.f_3_3_5_eval (x: Nat) : f_3_3_5 x = 7  :=
  _root_.Nat.F335.eq.Seven (x := x)

abbrev Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x  :=
  _root_.Set.Eq.is.All_Eq (X := X) (Y := Y) (f := f) (g := g)

abbrev SetTheory.Set.f_3_3_10_eq : f_3_3_10a = f_3_3_10b  :=
  _root_.Nat.F3310a.eq.F3310b

abbrev Function.comp_eval {X Y Z: Set} (g: Function Y Z) (f: Function X Y) (x: X) :
    (g ○ f) x = g (f x)  :=
  _root_.Set.Eq (X := X) (Y := Y) (Z := Z) (g := g) (f := f) (x := x)

abbrev Function.comp_eq_comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    (g ○ f).to_fn = g.to_fn ∘ f.to_fn  :=
  _root_.Set.ToFn.eq.ToFnToFn (X := X) (Y := Y) (Z := Z) (g := g) (f := f)

abbrev SetTheory.Set.g_circ_f_3_3_14 :
    g_3_3_14 ○ f_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+3:ℕ):Nat))  :=
  _root_.Nat.G3314F3314.eq.MkFn_AddMul2'3

abbrev SetTheory.Set.f_circ_g_3_3_14 :
    f_3_3_14 ○ g_3_3_14 = Function.mk_fn (fun x ↦ ((2*(x:ℕ)+6:ℕ):Nat))  :=
  _root_.Nat.F3314G3314.eq.MkFn_AddMul2'6

abbrev SetTheory.Set.comp_assoc {W X Y Z: Set} (h: Function Y Z) (g: Function X Y)
  (f: Function W X) :
    h ○ (g ○ f) = (h ○ g) ○ f  :=
  _root_.Set.Eq_SetTheory_Set_comp_assoc (W := W) (X := X) (Y := Y) (Z := Z) (g := g) (f := f) (h := h)

abbrev Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x'  :=
  _root_.Set.OneToOne.is.All_Eq (X := X) (Y := Y) (f := f)

abbrev Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn  :=
  _root_.Set.OneToOne.is.InjectiveToFn (X := X) (Y := Y) (f := f)

abbrev SetTheory.Set.f_3_3_18_one_to_one :
    (Function.mk_fn (fun (n:Nat) ↦ ((n^2:ℕ):Nat))).one_to_one  :=
  _root_.Nat.OneToOneMkFn_Square

abbrev SetTheory.Set.two_to_one {X Y: Set} {f: Function X Y} (h: ¬ f.one_to_one) :
    ∃ x x': X, x ≠ x' ∧ f x = f x'  :=
  _root_.Set.Any_And_Eq.of.NotOneToOne (X := X) (Y := Y) (f := f) (h := h)

abbrev Function.onto_iff {X Y: Set} (f: Function X Y) : f.onto ↔ Function.Surjective f.to_fn  :=
  _root_.Set.Onto.is.SurjectiveToFn (X := X) (Y := Y) (f := f)

abbrev Function.bijective_iff {X Y: Set} (f: Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn  :=
  _root_.Set.Bijective.is.BijectiveToFn (X := X) (Y := Y) (f := f)

abbrev Function.bijective_incorrect_def :
    ∃ X Y: Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective  :=
  _root_.Set.Any_Any_And_NotBijective

abbrev Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y  :=
  _root_.Set.Eq_GetInverse.is.Eq.of.Bijective (X := X) (Y := Y) (f := f) (y := y) (x := x) (h := h)

abbrev Function.inverse_eq {X Y: Set} [Nonempty X] {f: Function X Y} (h: f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn  :=
  _root_.Set.ToFnInverse.eq.InvFunToFn.of.Bijective (X := X) (Y := Y) (f := f) (h := h)

end Chapter3
