import Base
import ./material_cache.bend as Registry
import ./position.bend as P
import ./position_address.bend as Address
import ./table_cache.bend as Cache
import ./game.bend as Game
import ./dependency_engine.bend as Dependencies

# A completed stage holds a material directory. Stages are addressed by their
# explicit identifier, never by their current offset in the scheduler's list.
type Stage is Data:
  Stage{index: Nat, entries: List<&2, Registry.Named>}

def previous(index: Nat) -> Nat:
  match index:
    case 0n:
      0n
    case 1n+rest:
      rest

def equal(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 1n+x 1n+y:
      equal(x, y)
    case _ _:
      False{}

def choose(matches: Bool, entries: List<&2, Registry.Named>, later: Maybe<&2, List<&2, Registry.Named>>) -> Maybe<&2, List<&2, Registry.Named>>:
  match matches:
    case True{}:
      Some{entries}
    case False{}:
      later

def find(stages: List<&2, Stage>, +index: Nat) -> Maybe<&2, List<&2, Registry.Named>>:
  match stages:
    case Nil{}:
      None{}
    case Stage{number, entries} <> tail:
      choose(equal(index, number), entries, find(tail, index))

def in_stage(found: Maybe<&2, List<&2, Registry.Named>>, name: List<&2, P.Descriptor>) -> Maybe<&2, Cache.Entry>:
  match found:
    case None{}:
      None{}
    case Some{entries}:
      Registry.find(entries, name)

def select(stages: List<&2, Stage>, index: Nat, name: List<&2, P.Descriptor>) -> Maybe<&2, Cache.Entry>:
  in_stage(find(stages, index), name)

def read(found: Maybe<&2, List<&2, Registry.Named>>, address: Address.Address) -> Maybe<&2, Game.Outcome>:
  match found:
    case None{}:
      None{}
    case Some{entries}:
      Registry.resolve(entries, address)

def resolve(stages: List<&2, Stage>, index: Nat, address: Address.Address) -> Maybe<&2, Game.Outcome>:
  read(find(stages, index), address)

def Family(width: Nat) -> Data:
  Stage

# The scheduler owns the labels: a component builder only supplies its
# directory, so it cannot accidentally relabel a result as another stage.
def schedule(~C: Nat -> Data,
  ~build: @+stage: Nat -> @+width: Nat -> C(width) -> List<&2, Stage> -> List<&2, Registry.Named>,
  count: Nat, +width: Nat, context: C(width)) -> List<&2, Stage>:
  Dependencies.history(~C, ~Family,
    ~(+stage => +width => context => previous => Stage{stage, build(stage, width, context, previous)}),
    count, width, context)

def less(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 1n+rest:
      True{}
    case 1n+x 1n+y:
      less(x, y)
    case _ _:
      False{}

def Before(stages: List<&2, Stage>, +bound: Nat) -> Type:
  match stages:
    case Nil{}:
      Unit
    case Stage{index, entries} <> tail:
      Game.Truth(less(index, bound)) & Before(tail, bound)
