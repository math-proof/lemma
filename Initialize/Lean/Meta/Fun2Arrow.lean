/-
Rewrite helpers for `@[Fun]` / `@[Fun']`:
* binder types `Fun ι α` (notation `ι ⇀ α`) → bare arrows `ι → α`
* `GetElem.getElem` on a `Fun` collection → plain application
* `Fun.toFun` / `Fun` field-0 projection → the underlying function
* proof args for rewritten binders wrapped with `Fun.mk`
-/
import Def.Lean.Meta.Expr.Part4
open Lean

/-- Match `Fun ι α`, returning universe params and the two arguments. -/
def Lean.Expr.funType? : Expr → Option (List Level × Expr × Expr)
  | .app (.app (.const `Fun us) ι) α => some (us, ι, α)
  | _ => none

/-- `Fun ι α` → `ι → α` (anonymous default binder). -/
def Lean.Expr.funTypeToArrow (e : Expr) : Expr :=
  match e.funType? with
  | some (_, ι, α) => .forallE .anonymous ι α .default
  | none => e

/--
Pure expression rewrite used by `@[Fun]` / `@[Fun']`:
* `GetElem.getElem` whose collection type is `Fun _ _` becomes `xs i`
* `Fun.toFun _ _ f` and `f.toFun` (proj 0) become `f`
* recurses under app / forall / lam / let / proj / mdata

Does **not** change outer binder telescopes; callers rewrite those via `funTypeToArrow`
and wrap proof args with `Fun.mk` in `Expr.substFun`.
-/
def Lean.Expr.fun2arrow : Expr → Expr
  | app (app (app (app (app (app (app (app (const `GetElem.getElem us) coll) idx) elem) valid) inst) xs) i) isLt =>
    match coll.funType? with
    | some _ =>
      app xs.fun2arrow i.fun2arrow
    | none =>
      app
        (app
          (app
            (app
              (app
                (app
                  (app
                    (app (const `GetElem.getElem us) coll.fun2arrow)
                    idx.fun2arrow)
                  elem.fun2arrow)
                valid.fun2arrow)
              inst.fun2arrow)
            xs.fun2arrow)
          i.fun2arrow)
        isLt.fun2arrow
  | app (app (app (const `Fun.toFun _) _) _) f =>
    f.fun2arrow
  | proj `Fun 0 struct =>
    struct.fun2arrow
  | app fn arg =>
    app fn.fun2arrow arg.fun2arrow
  | forallE binderName binderType body binderInfo =>
    forallE binderName binderType.fun2arrow body.fun2arrow binderInfo
  | lam binderName binderType body binderInfo =>
    lam binderName binderType.fun2arrow body.fun2arrow binderInfo
  | letE declName type value body nondep =>
    letE declName type.fun2arrow value.fun2arrow body.fun2arrow nondep
  | proj typeName idx struct =>
    proj typeName idx struct.fun2arrow
  | mdata data expr =>
    mdata data expr.fun2arrow
  | expr => expr

/--
Build the `α →`-form sibling of a `Fun`/`⇀` theorem.

* Every outer binder whose type is `Fun ι α` becomes `ι → α` (v1: all Fun binders;
  `parity` reserved for a future bitmask like `@[fin]`, currently ignored).
* Body is rewritten with `fun2arrow` (GetElem → app, …).
* Proof reapplies `value` with `Fun.mk` wrappers on rewritten binders.
  Binder-type bvars are lifted into the full telescope (`incDeBruijnIndex (k+1)` for
  binder index `k` in the innermost-first `decompose_forallE` list).
-/
def Expr.substFun (type value : Lean.Expr) (_parity : Nat := 0) : Lean.Expr × Lean.Expr :=
  let ⟨binders, body⟩ := type.decompose_forallE
  let newBinders := binders.map fun ⟨binderName, binderType, binderInfo⟩ =>
    (binderName, binderType.funTypeToArrow.fun2arrow, binderInfo)
  let newBody := body.fun2arrow
  let telescope (lam : Name → Lean.Expr → Lean.Expr → BinderInfo → Lean.Expr) (b : Lean.Expr) :=
    newBinders.foldl
      (fun b ⟨binderName, binderType, binderInfo⟩ => lam binderName binderType b binderInfo)
      b
  let args : List Lean.Expr :=
    (List.range binders.length).zip binders |>.map fun ⟨k, binder⟩ =>
      let bv := Lean.Expr.bvar k
      let binderType := binder.2.1
      match binderType.funType? with
      | some (us, ι, α) =>
        -- binder types were stored under only the outer binders; lift into full telescope
        let lift := k + 1
        let ι := ι.incDeBruijnIndex lift
        let α := α.incDeBruijnIndex lift
        (Lean.Expr.const `Fun.mk us).mkApp [ι, α, bv]
      | none => bv
  let proofBody := value.mkApp args.reverse
  (telescope Lean.Expr.forallE newBody, telescope Lean.Expr.lam proofBody)
