import Base
import ./rules.bend as Rules
import ./encoding.bend as Encoding

# These finite cases establish arithmetic of one 6-bit square. They do not
# enumerate chess positions or evaluate any table entry.

def six(+f0: Bool, +f1: Bool, +f2: Bool,
  +r0: Bool, +r1: Bool, +r2: Bool) -> Word(6n):
  WCon{f0, WCon{f1, WCon{f2,
    WCon{r0, WCon{r1, WCon{r2, WNil{}}}}}}}

def add8_rank_bits(f0: Bool, f1: Bool,
  f2: Bool, r0: Bool, r1: Bool, r2: Bool) ->
  {Rules.rank(U32.add(Encoding.square(
     six(f0, f1, f2, r0, r1, r2)), 8)) ==
   U32.inc(Rules.rank(Encoding.square(
     six(f0, f1, f2, r0, r1, r2)))) : U32}:
  match f0 f1 f2 r0 r1 r2:
    case False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{}:
      {==}

def add8_rank(+bits: Word(6n)) ->
  {Rules.rank(U32.add(Encoding.square(bits), 8)) ==
   U32.inc(Rules.rank(Encoding.square(bits))) : U32}:
  match bits:
    case WCon{f0, WCon{f1, WCon{f2,
         WCon{r0, WCon{r1,
           WCon{r2, WNil{}}}}}}}:
      add8_rank_bits(f0, f1, f2, r0, r1, r2)

def add16_rank_bits(f0: Bool, f1: Bool,
  f2: Bool, r0: Bool, r1: Bool, r2: Bool) ->
  {Rules.rank(U32.add(Encoding.square(
     six(f0, f1, f2, r0, r1, r2)), 16)) ==
   U32.add(Rules.rank(Encoding.square(
     six(f0, f1, f2, r0, r1, r2))), 2) : U32}:
  match f0 f1 f2 r0 r1 r2:
    case False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{}:
      {==}

def add16_rank(+bits: Word(6n)) ->
  {Rules.rank(U32.add(Encoding.square(bits), 16)) ==
   U32.add(Rules.rank(Encoding.square(bits)), 2) : U32}:
  match bits:
    case WCon{f0, WCon{f1, WCon{f2,
         WCon{r0, WCon{r1,
           WCon{r2, WNil{}}}}}}}:
      add16_rank_bits(f0, f1, f2, r0, r1, r2)

def rank_below_max_bits(f0: Bool,
  f1: Bool, f2: Bool, r0: Bool,
  r1: Bool, r2: Bool) ->
  {U32.is_lt(Rules.rank(Encoding.square(
     six(f0, f1, f2, r0, r1, r2))),
   4294967295) == True{} : Bool}:
  match f0 f1 f2 r0 r1 r2:
    case False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{}:
      {==}

def rank_below_max(+bits: Word(6n)) ->
  {U32.is_lt(Rules.rank(
     Encoding.square(bits)),
   4294967295) == True{} : Bool}:
  match bits:
    case WCon{f0, WCon{f1, WCon{f2,
         WCon{r0, WCon{r1,
           WCon{r2, WNil{}}}}}}}:
      rank_below_max_bits(f0, f1,
        f2, r0, r1, r2)

def nat_rank_add8_bits(f0: Bool, f1: Bool,
  f2: Bool, r0: Bool, r1: Bool, r2: Bool) ->
  {U32.to_nat(Rules.rank(U32.add(
     Encoding.square(six(f0, f1, f2, r0, r1, r2)),
     8))) ==
   1n+U32.to_nat(Rules.rank(
     Encoding.square(six(f0, f1, f2, r0, r1, r2)))) : Nat}:
  match f0 f1 f2 r0 r1 r2:
    case False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{}:
      {==}

def nat_rank_add8(+bits: Word(6n)) ->
  {U32.to_nat(Rules.rank(U32.add(
     Encoding.square(bits), 8))) ==
   1n+U32.to_nat(Rules.rank(
     Encoding.square(bits))) : Nat}:
  match bits:
    case WCon{f0, WCon{f1, WCon{f2,
         WCon{r0, WCon{r1,
           WCon{r2, WNil{}}}}}}}:
      nat_rank_add8_bits(f0, f1, f2, r0, r1, r2)

def nat_rank_add16_bits(f0: Bool, f1: Bool,
  f2: Bool, r0: Bool, r1: Bool, r2: Bool) ->
  {U32.to_nat(Rules.rank(U32.add(
     Encoding.square(six(f0, f1, f2, r0, r1, r2)),
     16))) ==
   2n+U32.to_nat(Rules.rank(
     Encoding.square(six(f0, f1, f2, r0, r1, r2)))) : Nat}:
  match f0 f1 f2 r0 r1 r2:
    case False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{}:
      {==}

def nat_rank_add16(+bits: Word(6n)) ->
  {U32.to_nat(Rules.rank(U32.add(
     Encoding.square(bits), 16))) ==
   2n+U32.to_nat(Rules.rank(
     Encoding.square(bits))) : Nat}:
  match bits:
    case WCon{f0, WCon{f1, WCon{f2,
         WCon{r0, WCon{r1,
           WCon{r2, WNil{}}}}}}}:
      nat_rank_add16_bits(f0, f1, f2, r0, r1, r2)

def rank_positive_equiv_bits(f0: Bool, f1: Bool,
  f2: Bool, r0: Bool, r1: Bool, r2: Bool) ->
  {U32.is_gt(Rules.rank(Encoding.square(
     six(f0, f1, f2, r0, r1, r2))), 0) ==
   Nat.is_gt(U32.to_nat(Rules.rank(
     Encoding.square(six(f0, f1, f2, r0, r1, r2)))),
     0n) : Bool}:
  match f0 f1 f2 r0 r1 r2:
    case False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{}:
      {==}

def rank_positive_equiv(+bits: Word(6n)) ->
  {U32.is_gt(Rules.rank(
     Encoding.square(bits)), 0) ==
   Nat.is_gt(U32.to_nat(Rules.rank(
     Encoding.square(bits))), 0n) : Bool}:
  match bits:
    case WCon{f0, WCon{f1, WCon{f2,
         WCon{r0, WCon{r1,
           WCon{r2, WNil{}}}}}}}:
      rank_positive_equiv_bits(f0, f1, f2, r0, r1, r2)

def rank_below7_equiv_bits(f0: Bool, f1: Bool,
  f2: Bool, r0: Bool, r1: Bool, r2: Bool) ->
  {U32.is_lt(Rules.rank(Encoding.square(
     six(f0, f1, f2, r0, r1, r2))), 7) ==
   Nat.is_lt(U32.to_nat(Rules.rank(
     Encoding.square(six(f0, f1, f2, r0, r1, r2)))),
     7n) : Bool}:
  match f0 f1 f2 r0 r1 r2:
    case False{} False{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} False{} False{}:
      {==}
    case False{} False{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} True{} False{} False{} False{}:
      {==}
    case False{} False{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} True{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{} False{}:
      {==}
    case False{} False{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{} True{}:
      {==}
    case False{} False{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} False{} True{} True{}:
      {==}
    case False{} True{} False{} False{} True{} True{}:
      {==}
    case True{} True{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} True{} True{}:
      {==}
    case True{} False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} True{} True{}:
      {==}

def rank_below7_equiv(+bits: Word(6n)) ->
  {U32.is_lt(Rules.rank(
     Encoding.square(bits)), 7) ==
   Nat.is_lt(U32.to_nat(Rules.rank(
     Encoding.square(bits))), 7n) : Bool}:
  match bits:
    case WCon{f0, WCon{f1, WCon{f2,
         WCon{r0, WCon{r1,
           WCon{r2, WNil{}}}}}}}:
      rank_below7_equiv_bits(f0, f1, f2, r0, r1, r2)
