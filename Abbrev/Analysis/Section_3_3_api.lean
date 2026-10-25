import Abbrev.Analysis.Section_3_3_fn
import Abbrev.Analysis.Section_3_3_inv
import Lemma.Set.EqToFn
import Lemma.Set.EqIffP
import Lemma.Set.EqGetMkFn
import Lemma.Nat.P333a.Unique
import Lemma.Nat.Eq_F333a.is.Eq_Add_1
import Lemma.Nat.F333aNat.eq.Add_1
import Lemma.Nat.F333a4.eq.Five
import Lemma.Nat.F333a_AddMul2'3.eq.AddMul2'4
import Lemma.Nat.NotP333b.Unique
import Lemma.Set.P333c.Unique
import Lemma.Set.Eq_F333c.is.EqAdd_1
import Lemma.Nat.EqF333c_CoeNonzeroAdd_1
import Lemma.Nat.F333c_CoeNonzero4.eq.Three
import Lemma.Nat.F333c_CoeNonzeroAddMul2'3.eq.AddMul2'2
import Lemma.Nat.P335.Unique
import Lemma.Nat.F335.eq.Seven
import Lemma.Set.Eq.is.All_Eq
import Lemma.Nat.F3310a.eq.F3310b
import Lemma.Set.Eq
import Lemma.Set.ToFn.eq.ToFnToFn
import Lemma.Nat.G3314F3314.eq.MkFn_AddMul2'3
import Lemma.Nat.F3314G3314.eq.MkFn_AddMul2'6
import Lemma.Set.Eq_SetTheory_Set_comp_assoc
import Lemma.Set.OneToOne.is.All_Eq
import Lemma.Set.OneToOne.is.InjectiveToFn
import Lemma.Nat.OneToOneMkFn_Square
import Lemma.Set.Any_And_Eq.of.NotOneToOne
import Lemma.Set.Onto.is.SurjectiveToFn
import Lemma.Set.Bijective.is.BijectiveToFn
import Lemma.Set.Any_Any_And_NotBijective
import Lemma.Set.Eq_GetInverse.is.Eq.of.Bijective
import Lemma.Set.ToFnInverse.eq.InvFunToFn.of.Bijective


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
