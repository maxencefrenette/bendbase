import Base
import ./finite_table.bend as Finite

def prepend_get(depth: Nat, +width: Nat, +bit: Bool,
  +table: Finite.Table(depth, Word(width)), +key: Word(depth)) ->
  {Finite.get(depth, Word(1n+width), key, Finite.prepend(depth, width, bit, table)) ==
   WCon{bit, Finite.get(depth, Word(width), key, table)} : Word(1n+width)}:
  match depth table key:
    case 0n word WNil{}:
      {==}
    case 1n+rest Finite.Fork{left, right} WCon{False{}, tail}:
      prepend_get(rest, width, bit, left, tail)
    case 1n+rest Finite.Fork{left, right} WCon{True{}, tail}:
      prepend_get(rest, width, bit, right, tail)

def keys_get(n: Nat, +key: Word(n)) ->
  {Finite.get(n, Word(n), key, Finite.keys(n)) == key : Word(n)}:
  match n key:
    case 0n WNil{}:
      {==}
    case 1n++rest WCon{False{}, +tail}:
      %keys_get(rest, tail) :
        {Finite.get(1n+rest, Word(1n+rest), WCon{False{}, tail}, Finite.keys(1n+rest)) ==
          WCon{False{}, _} : Word(1n+rest)}
      prepend_get(rest, rest, False{}, Finite.keys(rest), tail)
    case 1n++rest WCon{True{}, +tail}:
      %keys_get(rest, tail) :
        {Finite.get(1n+rest, Word(1n+rest), WCon{True{}, tail}, Finite.keys(1n+rest)) ==
          WCon{True{}, _} : Word(1n+rest)}
      prepend_get(rest, rest, True{}, Finite.keys(rest), tail)

def add_assoc(a: Nat, +b: Nat, +c: Nat) ->
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) :
        {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def skip(n: Nat, +table: Finite.Table(n, U32), +acc: List<&2, U32>, +offset: Nat) ->
  {Finite.read(Finite.flatten.go(n, table, acc), Nat.add(Finite.size(n), offset)) ==
   Finite.read(acc, offset) : Maybe<&2, U32>}:
  match n table:
    case 0n byte:
      {==}
    case 1n++rest Finite.Fork{+left, +right}:
      +size = Finite.size(rest)
      Equal.trans(Maybe<&2, U32>,
        Finite.read(Finite.flatten.go(rest, left, Finite.flatten.go(rest, right, acc)),
          Nat.add(Nat.add(size, size), offset)),
        Finite.read(Finite.flatten.go(rest, left, Finite.flatten.go(rest, right, acc)),
          Nat.add(size, Nat.add(size, offset))),
        Finite.read(acc, offset),
        Equal.cong(Nat, Maybe<&2, U32>,
          i => Finite.read(Finite.flatten.go(rest, left, Finite.flatten.go(rest, right, acc)), i),
          Nat.add(Nat.add(size, size), offset), Nat.add(size, Nat.add(size, offset)),
          add_assoc(size, size, offset)),
        Equal.trans(Maybe<&2, U32>,
          Finite.read(Finite.flatten.go(rest, left, Finite.flatten.go(rest, right, acc)),
            Nat.add(size, Nat.add(size, offset))),
          Finite.read(Finite.flatten.go(rest, right, acc), Nat.add(size, offset)),
          Finite.read(acc, offset),
          skip(rest, left, Finite.flatten.go(rest, right, acc), Nat.add(size, offset)),
          skip(rest, right, acc, offset)))

def read_go(n: Nat, +table: Finite.Table(n, U32), +key: Word(n), +acc: List<&2, U32>) ->
  {Finite.read(Finite.flatten.go(n, table, acc), Finite.offset(n, key)) ==
   Some{Finite.get(n, U32, key, table)} : Maybe<&2, U32>}:
  match n table key:
    case 0n byte WNil{}:
      {==}
    case 1n++rest Finite.Fork{left, right} WCon{False{}, tail}:
      read_go(rest, left, tail, Finite.flatten.go(rest, right, acc))
    case 1n++rest Finite.Fork{+left, +right} WCon{True{}, +tail}:
      Equal.trans(Maybe<&2, U32>,
        Finite.read(Finite.flatten.go(rest, left, Finite.flatten.go(rest, right, acc)),
          Nat.add(Finite.size(rest), Finite.offset(rest, tail))),
        Finite.read(Finite.flatten.go(rest, right, acc), Finite.offset(rest, tail)),
        Some{Finite.get(rest, U32, tail, right)},
        skip(rest, left, Finite.flatten.go(rest, right, acc), Finite.offset(rest, tail)),
        read_go(rest, right, tail, acc))

def length_go(n: Nat, +table: Finite.Table(n, U32), +acc: List<&2, U32>) ->
  {List.length(&2, U32, Finite.flatten.go(n, table, acc)) ==
   Nat.add(Finite.size(n), List.length(&2, U32, acc)) : Nat}:
  match n table:
    case 0n byte:
      {==}
    case 1n++rest Finite.Fork{+left, +right}:
      +length = List.length(&2, U32, acc)
      +size = Finite.size(rest)
      Equal.trans(Nat,
        List.length(&2, U32, Finite.flatten.go(rest, left, Finite.flatten.go(rest, right, acc))),
        Nat.add(size, List.length(&2, U32, Finite.flatten.go(rest, right, acc))),
        Nat.add(Nat.add(size, size), length),
        length_go(rest, left, Finite.flatten.go(rest, right, acc)),
        Equal.trans(Nat,
          Nat.add(size, List.length(&2, U32, Finite.flatten.go(rest, right, acc))),
          Nat.add(size, Nat.add(size, length)), Nat.add(Nat.add(size, size), length),
          Equal.cong(Nat, Nat, x => Nat.add(size, x),
            List.length(&2, U32, Finite.flatten.go(rest, right, acc)),
            Nat.add(size, length), length_go(rest, right, acc)),
          Equal.sym(Nat, Nat.add(Nat.add(size, size), length),
            Nat.add(size, Nat.add(size, length)), add_assoc(size, size, length))))
