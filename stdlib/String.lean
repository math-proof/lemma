import Batteries.Data.String
import Lean.Meta
import stdlib.Lean.Char
open Lean.Meta
open Lean (Json JsonNumber)


def String.repeat (s : String) (n : Nat) : String :=
  String.join (List.replicate n s)


partial def countTailingZeros (n : Int) : Nat :=
  let rec loop (n : Int) (digits : Nat) : Nat :=
    if n == 0 || n % 10 != 0 then
      digits
    else
      loop (n / 10) (digits + 1)

  loop n 0

partial def String.printf (fmt : String) (args : List String) : String :=
  format fmt.toList args

where
  format (fmt : List Char) (args : List String) : String :=
    let i := fmt.idxOf '%'
    if i == fmt.length then
      fmt.asString
    else
      (fmt.take i).asString ++ format_after_percent (fmt.drop (i + 1)) args

  format_after_percent (fmt : List Char) (args : List String) : String :=
    match fmt with
    | '%' :: fmt =>
      "%" ++ format fmt args
    | '-' :: fmt =>
      parse_digits fmt args true
    | fmt =>
      parse_digits fmt args

  parse_digits (fmt : List Char) (args : List String) (left : Bool := false): String :=
    match args with
    | .nil =>
      let fmt := fmt.asString
      if left then
        "-" ++ fmt
      else
        fmt
    | arg :: args' =>
      let ⟨num, fmt⟩ := List.span Char.isDigit fmt
      match fmt with
      | .nil =>
        let s := num.asString
        if left then
          "-" ++ s
        else
          s

      | 's' :: fmt =>
        alignment num arg left ++ format fmt args'

      | '.' :: fmt =>
        let ⟨dec, fmt⟩ := List.span Char.isDigit fmt
        match fmt with
        | 'f' :: fmt =>
          let arg :=
            let json := Json.parse arg
            match json with
            | Except.ok arg =>
              match arg with
              | .num arg =>
                if dec.isEmpty then
                  arg.toString
                else
                  let dec := dec.asString.toNat!
                  let ⟨mantissa, exponent⟩ := arg
                  let mantissa :=
                    if exponent > dec then
                      let denominator := 10 ^ (exponent - dec)
                      let quotient := mantissa / denominator
                      if mantissa % denominator >= denominator / 2 then
                        quotient + 1
                      else
                        quotient
                    else if exponent < dec then
                      mantissa * (10 ^ (dec - exponent))
                    else
                      mantissa

                  let arg := JsonNumber.mk mantissa dec

                  let arg := arg.toString
                  if arg.posOf '.' == arg.endPos then
                    arg ++ "." ++ "0".repeat dec
                  else
                    let zeros := countTailingZeros mantissa
                    let zeros :=
                      if zeros > dec then
                        dec
                      else
                        zeros
                    arg ++ "0".repeat zeros
              | _ =>
                panic! "expected number"

            | Except.error e =>
              panic! e

          alignment num arg left ++ format fmt args'
        | _ =>
          let s := num.asString ++ "." ++ dec.asString ++ fmt.asString
          if left then
            "-" ++ s
          else
            s

      | ch :: fmt =>
        let s := ch.toString ++ format fmt args
        let s := num.asString ++ s
        if left then
          "-" ++ s
        else
          s

  alignment (num : List Char) (arg : String) (left : Bool) : String :=
    if num.isEmpty then
      arg
    else
      let num := num.asString.toNat!
      let padding := fun arg : String => " ".repeat (num - arg.length)
      if left then
        arg ++ padding arg
      else
        padding arg ++ arg


macro fmt:str ".format" args:term,+ : term => do
  `($(fmt).printf [$(← args.getElems.mapM fun arg => `(toString $arg)),*])


def String.implode := String.intercalate

def String.replaceFirst (s : String) (old new : String) : String :=
  match s.findSubstr? old with
  | none => s
  | some ⟨_, startPos, stopPos⟩ =>
    let before : Substring := ⟨s, 0, startPos⟩
    let after : Substring := ⟨s, stopPos, s.endPos⟩
    before.toString ++ new ++ after.toString


def String.escape_specials (s : String) : String :=
  -- extract the pattern from the string : ([a-zA-Z]+)_(.*)
  let ⟨head, tail⟩ := List.span (fun ch => ch.isAlpha || ch.isSubscriptDigit) s.toList
  if tail[0]? == some '_' then
    let tail := tail.drop 1
    let tail := String.mk <| tail.flatMap fun c =>
      if c == '{' then ['\\', '{']
      else if c == '}' then ['\\', '}']
      else if c == '_' then ['\\', '_']
      else [c]
    let formatStr :=
      match head.length with
      | 0 => "%s\\_%s"
      | 1 => "{%s}_{%s}"
      | _ =>  "{%s}\\_%s"
    formatStr.printf [String.mk head, tail]
  else s

def String.endsWithNumberedWord (s : String) (word : String) : Bool :=
  -- match the regexp expression : \\w+_\\d+
  if s.startsWith (word ++ "_") then
    let rest := s.drop (word.length + 1)
    rest.length ≥ 1 && rest.all Char.isDigit
  else
    false

def String.is_relational_operator : String → Bool
  | "et" | "ou" | "to" | "eq" | "ne" | "gt" | "lt" | "ge" | "le" | "in" | "as" | "dvd" | "subset" | "supset" => true
  | _ => false

def String.transformEq (first : String) : String :=
  if first.startsWith "Eq_" then
    "Eq" ++ first.drop 3
  else if first.startsWith "Eq" then
    "Eq_" ++ first.drop 2
  else if first.startsWith "SEq_" then
    "SEq" ++ first.drop 4
  else if first.startsWith "SEq" then
    "SEq_" ++ first.drop 3
  else if first.startsWith "Iff_" then
    "Iff" ++ first.drop 4
  else if first.startsWith "Iff" then
    "Iff_" ++ first.drop 3
  else
    panic! s!"Expected the operator to be '(S?Eq|Iff).*', got: {first}"

-- #eval "%%Hello %%%-10s! %5.2f%%".format "World", -20.666666 + 1
-- #eval "number: %4.2f".format -1
