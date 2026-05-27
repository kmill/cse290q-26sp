/-
Copyright (c) 2026 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

module
public import LilLean.Expr.Types

/-!
# Basic level constructions and functions
-/

public section

namespace LilLean

variable {ℓ ε : Type}

/--
Standard hash computation for expressions, given a function `getLevelHash` that
returns hashes for levels within `e` and `getExprHash` that returns hashes for
expressions within `e`.

Lowest two bits encode hasParam (bit 0) and hasMVar (bit 1).
The hash of `Level.zero` is `0`.

Offsets are incorporated in a simple way.
-/
def Expr.hashCore (e : Expr ℓ ε)
    (getLevelHash : ℓ → UInt64)
    (getExprHash : ε → UInt64) : UInt64 :=
  let mkHash (mixed : UInt64) (bits : UInt64) : UInt64 :=
    hashAddOffset ((mixed &&& ~~~3) ||| (bits &&& 3)) offset
  match u with
  | .zero => 0
  | .succ v =>
    let hv := getHash v
    hashAddOffset hv (offset + 1)
  | .max v w =>
    let hv := getHash v
    let hw := getHash w
    mkHash (mixHash 4 <| mixHash hv hw) (hv ||| hw)
  | .ipos v w =>
    let hv := getHash v
    let hw := getHash w
    mkHash (mixHash 5 <| mixHash hv hw) (hv ||| hw)
  | .param n =>
    let hn := hash n
    mkHash (mixHash 6 hn) 1
  | .mvar mvarId =>
    let hm := hash mvarId
    mkHash (mixHash 7 hm) 2
