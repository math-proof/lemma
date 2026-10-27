import Batteries.Data.String
import Lean.Meta
import Def.Lean.Char
open Lean.Meta
open Lean (Json JsonNumber)


def String.repeat (s : String) (n : Nat) : String :=
  String.join (List.replicate n s)

def String.eraseIdx (s : String) (n : Nat) : String :=
  (s.take n).toString ++ (s.drop n.succ).toString

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
      String.ofList fmt
    else
      String.ofList (fmt.take i) ++ format_after_percent (fmt.drop (i + 1)) args

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
      let fmt := String.ofList fmt
      if left then
        "-" ++ fmt
      else
        fmt
    | arg :: args' =>
      let ⟨num, fmt⟩ := List.span Char.isDigit fmt
      match fmt with
      | .nil =>
        let s := String.ofList num
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
                  let dec := (String.ofList dec).toNat!
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
                  if !arg.contains '.' then
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
          let s := String.ofList num ++ "." ++ String.ofList dec ++ String.ofList fmt
          if left then
            "-" ++ s
          else
            s

      | ch :: fmt =>
        let s := ch.toString ++ format fmt args
        let s := String.ofList num ++ s
        if left then
          "-" ++ s
        else
          s

  alignment (num : List Char) (arg : String) (left : Bool) : String :=
    if num.isEmpty then
      arg
    else
      let num := (String.ofList num).toNat!
      let padding := fun arg : String => " ".repeat (num - arg.length)
      if left then
        arg ++ padding arg
      else
        padding arg ++ arg


