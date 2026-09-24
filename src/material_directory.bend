import Base
import ./position.bend as P
import ./pawnless_chess.bend as Chess
import ./position_index.bend as Index
import ./finite_table.bend as Finite
import ./game.bend as Game
import ./material_cache.bend as Registry
import ./table_cache.bend as Cache
import ./component_cache.bend as Stages

# All non-king kinds, for both relative owners. No material-family cases.
def descriptors() -> List<&2, P.Descriptor>:
  [P.Descriptor{False{}, P.Pawn{}}, P.Descriptor{False{}, P.Piece{Chess.Queen{}}},
   P.Descriptor{False{}, P.Piece{Chess.Rook{}}}, P.Descriptor{False{}, P.Piece{Chess.Bishop{}}},
   P.Descriptor{False{}, P.Piece{Chess.Knight{}}}, P.Descriptor{True{}, P.Pawn{}},
   P.Descriptor{True{}, P.Piece{Chess.Queen{}}}, P.Descriptor{True{}, P.Piece{Chess.Rook{}}},
   P.Descriptor{True{}, P.Piece{Chess.Bishop{}}}, P.Descriptor{True{}, P.Piece{Chess.Knight{}}}]

def prefix(+head: P.Descriptor, tails: List<&2, List<&2, P.Descriptor>>) -> List<&2, List<&2, P.Descriptor>>:
  match tails:
    case Nil{}:
      Nil{}
    case tail <> rest:
      (head <> tail) <> prefix(head, rest)

def products(heads: List<&2, P.Descriptor>, +tails: List<&2, List<&2, P.Descriptor>>) -> List<&2, List<&2, P.Descriptor>>:
  match heads:
    case Nil{}:
      Nil{}
    case head <> rest:
      List.append(&2, List<&2, P.Descriptor>, prefix(head, tails), products(rest, tails))

# Every ordered signature with at most capacity non-kings, including KK.
# This enumerates material signatures at generation time, NOT positions in
# the proof. Completeness is induction on capacity and the queried signature.
def names(capacity: Nat) -> List<&2, List<&2, P.Descriptor>>:
  match capacity:
    case 0n:
      [Nil{}]
    case 1n+rest:
      Nil{} <> products(descriptors(), names(rest))

def width(name: List<&2, P.Descriptor>) -> Nat:
  Index.width(List.length(&2, P.Descriptor, name))

def entry(~C: Data, ~solve: @+name: List<&2, P.Descriptor> -> C -> Finite.Table(width(name), Game.Outcome),
  +name: List<&2, P.Descriptor>, context: C) -> Cache.Entry:
  Cache.Entry{width(name), solve(name, context)}

def register(~C: Data, ~solve: @+name: List<&2, P.Descriptor> -> C -> Finite.Table(width(name), Game.Outcome),
  names: List<&2, List<&2, P.Descriptor>>, +context: C) -> List<&2, Registry.Named>:
  match names:
    case Nil{}:
      Nil{}
    case +name <> rest:
      Registry.Named{name, entry(~C, ~solve, name, context)} <> register(~C, ~solve, rest, context)

def build(~C: Data, ~solve: @+name: List<&2, P.Descriptor> -> C -> Finite.Table(width(name), Game.Outcome),
  capacity: Nat, context: C) -> List<&2, Registry.Named>:
  register(~C, ~solve, names(capacity), context)

type Work<-C: Data> is Data:
  Work{stage: Nat, context: C, previous: List<&2, Stages.Stage>}

def solve_work(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(width(name), Game.Outcome),
  +name: List<&2, P.Descriptor>, work: Work<C>) -> Finite.Table(width(name), Game.Outcome):
  match work:
    case Work{stage, context, previous}:
      solve(name, stage, context, previous)

def stage(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(width(name), Game.Outcome),
  index: Nat, capacity: Nat, context: C, previous: List<&2, Stages.Stage>) -> List<&2, Registry.Named>:
  build(~Work<C>, ~(+name => work => solve_work(~C, ~solve, name, work)), capacity, Work{index, context, previous})

def schedule(~C: Data,
  ~solve: @+name: List<&2, P.Descriptor> -> Nat -> C -> List<&2, Stages.Stage> -> Finite.Table(width(name), Game.Outcome),
  count: Nat, capacity: Nat, context: C) -> List<&2, Stages.Stage>:
  Stages.schedule(~(width => C),
    ~(+index => +capacity => context => previous => stage(~C, ~solve, index, capacity, context, previous)), count, capacity, context)

def Available(stages: List<&2, Stages.Stage>, index: Nat, +name: List<&2, P.Descriptor>) -> Type:
  &table: Finite.Table(width(name), Game.Outcome) ->
    {Stages.select(stages, index, name) == Some{Cache.Entry{width(name), table}} : Maybe<&2, Cache.Entry>}

def Member(-A: Data, +value: A, values: List<&2, A>) -> Type:
  match values:
    case Nil{}:
      Empty
    case head <> tail:
      {value == head : A} | Member(A, value, tail)
