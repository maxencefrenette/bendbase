import Base
import ./component_cache.bend as Stages
import ./material_cache.bend as Registry
import ./material_cache_proof.bend as RegistryProof
import ./position.bend as P
import ./table_cache.bend as Cache
import ./game.bend as Game
import ./position_address.bend as Address
import ./position_index.bend as Index
import ./finite_table.bend as Finite

def equal_refl(+n: Nat) -> {Stages.equal(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+rest:
      equal_refl(rest)

def equal_reflect(+a: Nat, +b: Nat, evidence: Game.Truth(Stages.equal(a, b))) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+rest:
      match evidence:
    case 1n+rest 0n:
      match evidence:
    case 1n+x 1n+y:
      %equal_reflect(x, y, evidence) : {1n+x == 1n+_ : Nat}
      {==}

def next_differs(+n: Nat) -> {Stages.equal(n, 1n+n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+rest:
      next_differs(rest)

def find_head(+index: Nat, +entries: List<&2, Registry.Named>, +tail: List<&2, Stages.Stage>) ->
  {Stages.find(Stages.Stage{index, entries} <> tail, index) == Some{entries} : Maybe<&2, List<&2, Registry.Named>>}:
  %Equal.sym(Bool, Stages.equal(index, index), True{}, equal_refl(index)) :
    {Stages.choose(_, entries, Stages.find(tail, index)) == Some{entries} : Maybe<&2, List<&2, Registry.Named>>}
  {==}

def select_head(+index: Nat, +name: List<&2, P.Descriptor>, +entry: Cache.Entry, +tail: List<&2, Stages.Stage>) ->
  {Stages.select(Stages.Stage{index, [Registry.Named{name, entry}]} <> tail, index, name) == Some{entry} : Maybe<&2, Cache.Entry>}:
  %Equal.sym(Maybe<&2, List<&2, Registry.Named>>,
    Stages.find(Stages.Stage{index, [Registry.Named{name, entry}]} <> tail, index), Some{[Registry.Named{name, entry}]},
    find_head(index, [Registry.Named{name, entry}], tail)) :
    {Stages.in_stage(_, name) == Some{entry} : Maybe<&2, Cache.Entry>}
  RegistryProof.find_head(name, entry, Nil{})

def resolve_head(+index: Nat, +n: Nat, +material: P.Material(n), +key: Word(Index.width(n)),
  +table: Finite.Table(Index.width(n), Game.Outcome), +tail: List<&2, Stages.Stage>) ->
  {Stages.resolve(Stages.Stage{index, [Registry.Named{Registry.signature(n, material), Cache.Entry{Index.width(n), table}}]} <> tail,
     index, Address.Address{n, material, key}) == Some{Finite.get(Index.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}:
  +entries = {[Registry.Named{Registry.signature(n, material), Cache.Entry{Index.width(n), table}}] : List<&2, Registry.Named>}
  %Equal.sym(Maybe<&2, List<&2, Registry.Named>>,
    Stages.find(Stages.Stage{index, entries} <> tail, index), Some{entries}, find_head(index, entries, tail)) :
    {Stages.read(_, Address.Address{n, material, key}) == Some{Finite.get(Index.width(n), Game.Outcome, key, table)} : Maybe<&2, Game.Outcome>}
  RegistryProof.resolve_head(n, material, key, table, Nil{})

def skip_next(+index: Nat, +entries: List<&2, Registry.Named>, +tail: List<&2, Stages.Stage>, +name: List<&2, P.Descriptor>) ->
  {Stages.select(Stages.Stage{1n+index, entries} <> tail, index, name) == Stages.select(tail, index, name) : Maybe<&2, Cache.Entry>}:
  %Equal.sym(Bool, Stages.equal(index, 1n+index), False{}, next_differs(index)) :
    {Stages.in_stage(Stages.choose(_, entries, Stages.find(tail, index)), name) == Stages.select(tail, index, name) : Maybe<&2, Cache.Entry>}
  {==}

def less_next(+n: Nat) -> Game.Truth(Stages.less(n, 1n+n)):
  match n:
    case 0n:
      Unit{}
    case 1n+rest:
      less_next(rest)

def less_weaken(+a: Nat, +b: Nat, evidence: Game.Truth(Stages.less(a, b))) -> Game.Truth(Stages.less(a, 1n+b)):
  match a b:
    case 0n 0n:
      match evidence:
    case 0n 1n+rest:
      Unit{}
    case 1n+rest 0n:
      match evidence:
    case 1n+x 1n+y:
      less_weaken(x, y, evidence)

def before_weaken(+stages: List<&2, Stages.Stage>, +bound: Nat, evidence: Stages.Before(stages, bound)) ->
  Stages.Before(stages, 1n+bound):
  match stages evidence:
    case Nil{} Unit{}:
      Unit{}
    case Stages.Stage{index, entries} <> tail Tuple{earlier, rest}:
      (less_weaken(index, bound, earlier), before_weaken(tail, bound, rest))

def schedule_before(~C: Nat -> Data,
  ~build: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, Stages.Stage> -> List<&2, Registry.Named>,
  count: Nat, +width: Nat, +context: C(width)) ->
  Stages.Before(Stages.schedule(~C, ~build, count, width, context), 1n+count):
  match count:
    case 0n:
      Unit{}
    case 1n++prior:
      (less_next(1n+prior), before_weaken(Stages.schedule(~C, ~build, prior, width, context), 1n+prior,
        schedule_before(~C, ~build, prior, width, context)))

def less_not_equal(+a: Nat, +b: Nat, evidence: Game.Truth(Stages.less(a, b))) ->
  {Stages.equal(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      match evidence:
    case 0n 1n+rest:
      {==}
    case 1n+rest 0n:
      match evidence:
    case 1n+x 1n+y:
      less_not_equal(x, y, evidence)

def current_missing(+stages: List<&2, Stages.Stage>, +bound: Nat, evidence: Stages.Before(stages, bound)) ->
  {Stages.find(stages, bound) == None{} : Maybe<&2, List<&2, Registry.Named>>}:
  match stages evidence:
    case Nil{} Unit{}:
      {==}
    case Stages.Stage{index, entries} <> tail Tuple{earlier, rest}:
      %Equal.sym(Bool, Stages.equal(bound, index), False{}, less_not_equal(index, bound, earlier)) :
        {Stages.choose(_, entries, Stages.find(tail, bound)) == None{} : Maybe<&2, List<&2, Registry.Named>>}
      current_missing(tail, bound, rest)
