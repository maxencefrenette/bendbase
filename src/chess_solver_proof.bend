import Base
import ./chess_solver.bend as Compile
import ./clock_solver.bend as Solver
import ./clock_solver_proof.bend as SolverProof
import ./chess_graph.bend as Graph
import ./chess_cache.bend as Cache
import ./table_cache.bend as Tables
import ./component_cache.bend as Stages
import ./position_address.bend as Address
import ./position_index.bend as Index
import ./position.bend as P
import ./material_directory.bend as Directory
import ./finite_table.bend as Finite
import ./finite_table_proof.bend as FiniteProof
import ./table_cache_proof.bend as TableProof
import ./game.bend as Game
import ./table_engine.bend as Engine

# Proof observations of the compiler and of the original addressed graph.
# These are one-step Bellman values, not another recursive chess solver.
def key_value(+width: Nat, key: Maybe<&2, Word(width)>, previous: Finite.Table(width, Game.Outcome)) -> Maybe<&2, Game.Outcome>:
  match key:
    case None{}:
      None{}
    case Some{word}:
      Some{Finite.get(width, Game.Outcome, word, previous)}

def edge_value(+width: Nat, edge: Maybe<&2, Solver.Edge<width>>, previous: Finite.Table(width, Game.Outcome)) -> Maybe<&2, Game.Outcome>:
  match edge:
    case None{}:
      None{}
    case Some{edge}:
      Some{Solver.edge_value(width, edge, previous)}

def source_value(+width: Nat, stages: List<&2, Stages.Stage>, edge: Graph.Edge, previous: Finite.Table(width, Game.Outcome)) -> Maybe<&2, Game.Outcome>:
  match edge:
    case Graph.Quiet{Address.Address{n, material, word}}:
      Tables.read(width, Index.width(n), word, previous)
    case Graph.Reset{address}:
      Cache.resolve(stages, address)

def key_exact(+width: Nat, +word: Word(width)) -> {Compile.key(width, width, word) == Some{word} : Maybe<&2, Word(width)>}:
  match width word:
    case 0n WNil{}:
      {==}
    case 1n+rest WCon{bit, tail}:
      Equal.cong(Maybe<&2, Word(rest)>, Maybe<&2, Word(1n+rest)>, key => Compile.put_bit(rest, bit, key),
        Compile.key(rest, rest, tail), Some{tail}, key_exact(rest, tail))

def put_value(+width: Nat, +bit: Bool, +key: Maybe<&2, Word(width)>, +left: Finite.Table(width, Game.Outcome), +right: Finite.Table(width, Game.Outcome)) ->
  {key_value(1n+width, Compile.put_bit(width, bit, key), Finite.Fork{left, right}) ==
    key_value(width, key, Bool.pick(Finite.Table(width, Game.Outcome), bit, right, left)) : Maybe<&2, Game.Outcome>}:
  match bit key:
    case False{} None{}:
      {==}
    case True{} None{}:
      {==}
    case False{} Some{word}:
      {==}
    case True{} Some{word}:
      {==}

def key_read(+target: Nat, +source: Nat, +word: Word(source), +previous: Finite.Table(target, Game.Outcome)) ->
  {key_value(target, Compile.key(source, target, word), previous) == Tables.read(target, source, word, previous) : Maybe<&2, Game.Outcome>}:
  match target source word previous:
    case 0n 0n WNil{} value:
      {==}
    case 0n 1n+rest word value:
      {==}
    case 1n+rest 0n WNil{} table:
      {==}
    case 1n+rest 1n+more WCon{False{}, tail} Finite.Fork{left, right}:
      Equal.trans(Maybe<&2, Game.Outcome>, key_value(target, Compile.key(source, target, word), previous),
        key_value(rest, Compile.key(more, rest, tail), left), Tables.read(rest, more, tail, left),
        put_value(rest, False{}, Compile.key(more, rest, tail), left, right), key_read(rest, more, tail, left))
    case 1n+rest 1n+more WCon{True{}, tail} Finite.Fork{left, right}:
      Equal.trans(Maybe<&2, Game.Outcome>, key_value(target, Compile.key(source, target, word), previous),
        key_value(rest, Compile.key(more, rest, tail), right), Tables.read(rest, more, tail, right),
        put_value(rest, True{}, Compile.key(more, rest, tail), left, right), key_read(rest, more, tail, right))

def quiet_value(+width: Nat, +key: Maybe<&2, Word(width)>, +previous: Finite.Table(width, Game.Outcome)) ->
  {edge_value(width, Compile.quiet(width, key), previous) == key_value(width, key, previous) : Maybe<&2, Game.Outcome>}:
  match key:
    case None{}:
      {==}
    case Some{word}:
      {==}

def reset_value(+width: Nat, +result: Maybe<&2, Game.Outcome>, +previous: Finite.Table(width, Game.Outcome)) ->
  {edge_value(width, Cache.reset_value(width, result), previous) == result : Maybe<&2, Game.Outcome>}:
  match result:
    case None{}:
      {==}
    case Some{result}:
      {==}

def edge(+width: Nat, +stages: List<&2, Stages.Stage>, +original: Graph.Edge, +previous: Finite.Table(width, Game.Outcome)) ->
  {edge_value(width, Compile.edge(width, stages, original), previous) == source_value(width, stages, original, previous) : Maybe<&2, Game.Outcome>}:
  match original:
    case Graph.Quiet{Address.Address{n, material, word}}:
      Equal.trans(Maybe<&2, Game.Outcome>, edge_value(width, Compile.edge(width, stages, original), previous),
        key_value(width, Compile.key(Index.width(n), width, word), previous), source_value(width, stages, original, previous),
        quiet_value(width, Compile.key(Index.width(n), width, word), previous), key_read(width, Index.width(n), word, previous))
    case Graph.Reset{address}:
      reset_value(width, Cache.resolve(stages, address), previous)

def values(+width: Nat, edges: Maybe<&2, List<&2, Solver.Edge<width>>>, previous: Finite.Table(width, Game.Outcome)) -> Maybe<&2, List<&2, Game.Outcome>>:
  match edges:
    case None{}:
      None{}
    case Some{edges}:
      Some{Solver.values(width, edges, previous)}

def cons_value(head: Maybe<&2, Game.Outcome>, tail: Maybe<&2, List<&2, Game.Outcome>>) -> Maybe<&2, List<&2, Game.Outcome>>:
  match head tail:
    case Some{head} Some{tail}:
      Some{head <> tail}
    case _ _:
      None{}

def source_values(+width: Nat, +stages: List<&2, Stages.Stage>, children: List<&2, Graph.Edge>, +previous: Finite.Table(width, Game.Outcome)) -> Maybe<&2, List<&2, Game.Outcome>>:
  match children:
    case Nil{}:
      Some{Nil{}}
    case head <> tail:
      cons_value(source_value(width, stages, head, previous), source_values(width, stages, tail, previous))

def cons_values(+width: Nat, +head: Maybe<&2, Solver.Edge<width>>, +tail: Maybe<&2, List<&2, Solver.Edge<width>>>, +previous: Finite.Table(width, Game.Outcome)) ->
  {values(width, Compile.cons(width, head, tail), previous) == cons_value(edge_value(width, head, previous), values(width, tail, previous)) : Maybe<&2, List<&2, Game.Outcome>>}:
  match head tail:
    case None{} _:
      {==}
    case Some{head} None{}:
      {==}
    case Some{head} Some{tail}:
      {==}

def edges(+width: Nat, +stages: List<&2, Stages.Stage>, +children: List<&2, Graph.Edge>, +previous: Finite.Table(width, Game.Outcome)) ->
  {values(width, Compile.edges(width, stages, children), previous) == source_values(width, stages, children, previous) : Maybe<&2, List<&2, Game.Outcome>>}:
  match children:
    case Nil{}:
      {==}
    case +head <> +tail:
      %Equal.sym(Maybe<&2, List<&2, Game.Outcome>>, values(width, Compile.edges(width, stages, children), previous),
        cons_value(edge_value(width, Compile.edge(width, stages, head), previous), values(width, Compile.edges(width, stages, tail), previous)),
        cons_values(width, Compile.edge(width, stages, head), Compile.edges(width, stages, tail), previous)) :
        {_ == source_values(width, stages, children, previous) : Maybe<&2, List<&2, Game.Outcome>>}
      %edge(width, stages, head, previous) :
        {cons_value(edge_value(width, Compile.edge(width, stages, head), previous), values(width, Compile.edges(width, stages, tail), previous)) ==
          cons_value(_, source_values(width, stages, tail, previous)) : Maybe<&2, List<&2, Game.Outcome>>}
      %edges(width, stages, tail, previous) :
        {cons_value(edge_value(width, Compile.edge(width, stages, head), previous), values(width, Compile.edges(width, stages, tail), previous)) ==
          cons_value(edge_value(width, Compile.edge(width, stages, head), previous), _) : Maybe<&2, List<&2, Game.Outcome>>}
      {==}

def fold(turn: Game.Player, results: Maybe<&2, List<&2, Game.Outcome>>) -> Maybe<&2, Game.Outcome>:
  match results:
    case None{}:
      None{}
    case Some{Nil{}}:
      Some{Game.Draw{}}
    case Some{head <> tail}:
      Some{Engine.fold(tail, turn, head)}

def backup(+width: Nat, stages: List<&2, Stages.Stage>, node: Graph.Node, previous: Finite.Table(width, Game.Outcome)) -> Maybe<&2, Game.Outcome>:
  match node:
    case Graph.Terminal{result}:
      Some{result}
    case Graph.Choice{turn, children}:
      fold(turn, source_values(width, stages, children, previous))

def node_value(+width: Nat, node: Maybe<&2, Solver.Node<width>>, previous: Finite.Table(width, Game.Outcome)) -> Maybe<&2, Game.Outcome>:
  match node:
    case None{}:
      None{}
    case Some{node}:
      Some{Solver.at(width, Solver.Next{previous}, node)}

def choice_value(+width: Nat, +turn: Game.Player, +children: Maybe<&2, List<&2, Solver.Edge<width>>>, +previous: Finite.Table(width, Game.Outcome)) ->
  {node_value(width, Compile.choice(width, turn, children), previous) == fold(turn, values(width, children, previous)) : Maybe<&2, Game.Outcome>}:
  match children:
    case None{}:
      {==}
    case Some{Nil{}}:
      {==}
    case Some{head <> tail}:
      {==}

def node(+width: Nat, +stages: List<&2, Stages.Stage>, +original: Graph.Node, +previous: Finite.Table(width, Game.Outcome)) ->
  {node_value(width, Compile.node(width, stages, original), previous) == backup(width, stages, original, previous) : Maybe<&2, Game.Outcome>}:
  match original:
    case Graph.Terminal{result}:
      {==}
    case Graph.Choice{turn, children}:
      Equal.trans(Maybe<&2, Game.Outcome>, node_value(width, Compile.node(width, stages, original), previous),
        fold(turn, values(width, Compile.edges(width, stages, children), previous)), backup(width, stages, original, previous),
        choice_value(width, turn, Compile.edges(width, stages, children), previous),
        Equal.cong(Maybe<&2, List<&2, Game.Outcome>>, Maybe<&2, Game.Outcome>, outcomes => fold(turn, outcomes),
          values(width, Compile.edges(width, stages, children), previous), source_values(width, stages, children, previous), edges(width, stages, children, previous)))

def table_value(+width: Nat, table: Maybe<&2, Finite.Table(width, Game.Outcome)>, key: Word(width)) -> Maybe<&2, Game.Outcome>:
  match table:
    case None{}:
      None{}
    case Some{table}:
      Some{Finite.get(width, Game.Outcome, key, table)}

def solved(+remaining: Nat, +width: Nat, +graph: Finite.Table(width, Solver.Node<width>), +key: Word(width)) ->
  {table_value(width, Compile.solve(remaining, width, Some{graph}), key) == Some{Game.evaluate(Solver.tree(remaining, width, graph, key))} : Maybe<&2, Game.Outcome>}:
  Equal.cong(Game.Outcome, Maybe<&2, Game.Outcome>, result => Some{result}, Finite.get(width, Game.Outcome, key, Solver.generate(remaining, width, graph)),
    Game.evaluate(Solver.tree(remaining, width, graph, key)), SolverProof.pointwise(remaining, width, graph, key))

def component(+name: List<&2, P.Descriptor>, +stage: Nat, +limit: Nat, +stages: List<&2, Stages.Stage>,
  +graph: Finite.Table(Directory.width(name), Solver.Node<Directory.width(name)>), +key: Word(Directory.width(name)),
  compiled: {Compile.graph(name, stage, stages) == Some{graph} : Maybe<&2, Finite.Table(Directory.width(name), Solver.Node<Directory.width(name)>)>}) ->
  {table_value(Directory.width(name), Compile.component(name, stage, limit, stages), key) == Some{Game.evaluate(Solver.tree(limit, Directory.width(name), graph, key))} : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Maybe<&2, Finite.Table(Directory.width(name), Solver.Node<Directory.width(name)>)>, Compile.graph(name, stage, stages), Some{graph}, compiled) :
    {table_value(Directory.width(name), Compile.solve(limit, Directory.width(name), _), key) == Some{Game.evaluate(Solver.tree(limit, Directory.width(name), graph, key))} : Maybe<&2, Game.Outcome>}
  solved(limit, Directory.width(name), graph, key)

def present(-A: Data, value: Maybe<&2, A>) -> Type:
  match value:
    case None{}:
      Empty
    case Some{value}:
      Unit

def impossible(-A: Data, +value: A, equality: {None{} == Some{value} : Maybe<&2, A>}) -> Empty:
  %Equal.sym(Maybe<&2, A>, None{}, Some{value}, equality) : present(A, _)
  Unit{}

def branch(-depth: Nat, -width: Nat, bit: Bool, tree: Finite.Table(1n+depth, Solver.Node<width>)) -> Finite.Table(depth, Solver.Node<width>):
  match bit tree:
    case False{} Finite.Fork{left, right}:
      left
    case True{} Finite.Fork{left, right}:
      right

def select(-A: Data, bit: Bool, left: A, right: A) -> A:
  match bit:
    case False{}:
      left
    case True{}:
      right

def child_value(-depth: Nat, -width: Nat, bit: Bool, tree: Maybe<&2, Finite.Table(1n+depth, Solver.Node<width>)>) -> Maybe<&2, Finite.Table(depth, Solver.Node<width>)>:
  match tree:
    case None{}:
      None{}
    case Some{tree}:
      Some{branch(depth, width, bit, tree)}

def fork_child(+depth: Nat, +width: Nat, +bit: Bool,
  +left: Maybe<&2, Finite.Table(depth, Solver.Node<width>)>, +right: Maybe<&2, Finite.Table(depth, Solver.Node<width>)>,
  +tree: Finite.Table(1n+depth, Solver.Node<width>),
  built: {Compile.fork(depth, width, left, right) == Some{tree} : Maybe<&2, Finite.Table(1n+depth, Solver.Node<width>)>}) ->
  {select(Maybe<&2, Finite.Table(depth, Solver.Node<width>)>, bit, left, right) == Some{branch(depth, width, bit, tree)} : Maybe<&2, Finite.Table(depth, Solver.Node<width>)>}:
  match bit left right:
    case bit None{} right:
      TableProof.absurd({select(Maybe<&2, Finite.Table(depth, Solver.Node<width>)>, bit, None{}, right) == Some{branch(depth, width, bit, tree)} : Maybe<&2, Finite.Table(depth, Solver.Node<width>)>}, impossible(Finite.Table(1n+depth, Solver.Node<width>), tree, built))
    case bit Some{left} None{}:
      TableProof.absurd({select(Maybe<&2, Finite.Table(depth, Solver.Node<width>)>, bit, Some{left}, None{}) == Some{branch(depth, width, bit, tree)} : Maybe<&2, Finite.Table(depth, Solver.Node<width>)>}, impossible(Finite.Table(1n+depth, Solver.Node<width>), tree, built))
    case False{} Some{left} Some{right}:
      Equal.cong(Maybe<&2, Finite.Table(1n+depth, Solver.Node<width>)>, Maybe<&2, Finite.Table(depth, Solver.Node<width>)>,
        value => child_value(depth, width, False{}, value), Some{Finite.Fork{left, right}}, Some{tree}, built)
    case True{} Some{left} Some{right}:
      Equal.cong(Maybe<&2, Finite.Table(1n+depth, Solver.Node<width>)>, Maybe<&2, Finite.Table(depth, Solver.Node<width>)>,
        value => child_value(depth, width, True{}, value), Some{Finite.Fork{left, right}}, Some{tree}, built)

def fill(+depth: Nat, +name: List<&2, P.Descriptor>, +stage: Nat, +stages: List<&2, Stages.Stage>,
  +keys: Finite.Table(depth, Word(Directory.width(name))), +tree: Finite.Table(depth, Solver.Node<Directory.width(name)>), +key: Word(depth),
  built: {Compile.fill(depth, name, stage, stages, keys) == Some{tree} : Maybe<&2, Finite.Table(depth, Solver.Node<Directory.width(name)>)>}) ->
  {Compile.entry(name, stage, stages, Finite.get(depth, Word(Directory.width(name)), key, keys)) ==
    Some{Finite.get(depth, Solver.Node<Directory.width(name)>, key, tree)} : Maybe<&2, Solver.Node<Directory.width(name)>>}:
  match depth keys tree key:
    case 0n original node WNil{}:
      built
    case 1n++rest Finite.Fork{left, right} Finite.Fork{a, b} WCon{False{}, tail}:
      fill(rest, name, stage, stages, left, a, tail,
        fork_child(rest, Directory.width(name), False{}, Compile.fill(rest, name, stage, stages, left), Compile.fill(rest, name, stage, stages, right), Finite.Fork{a, b}, built))
    case 1n++rest Finite.Fork{left, right} Finite.Fork{a, b} WCon{True{}, tail}:
      fill(rest, name, stage, stages, right, b, tail,
        fork_child(rest, Directory.width(name), True{}, Compile.fill(rest, name, stage, stages, left), Compile.fill(rest, name, stage, stages, right), Finite.Fork{a, b}, built))

def graph(+name: List<&2, P.Descriptor>, +stage: Nat, +stages: List<&2, Stages.Stage>,
  +tree: Finite.Table(Directory.width(name), Solver.Node<Directory.width(name)>), +key: Word(Directory.width(name)),
  built: {Compile.graph(name, stage, stages) == Some{tree} : Maybe<&2, Finite.Table(Directory.width(name), Solver.Node<Directory.width(name)>)>}) ->
  {Compile.entry(name, stage, stages, key) == Some{Finite.get(Directory.width(name), Solver.Node<Directory.width(name)>, key, tree)} : Maybe<&2, Solver.Node<Directory.width(name)>>}:
  %FiniteProof.keys_get(Directory.width(name), key) :
    {Compile.entry(name, stage, stages, _) == Some{Finite.get(Directory.width(name), Solver.Node<Directory.width(name)>, key, tree)} : Maybe<&2, Solver.Node<Directory.width(name)>>}
  fill(Directory.width(name), name, stage, stages, Finite.keys(Directory.width(name)), tree, key, built)

# Connect the actual generated layer, not just a stand-alone compiled node,
# to the addressed entry's Bellman step at the same symbolic position key.
def layer(+name: List<&2, P.Descriptor>, +stage: Nat, +stages: List<&2, Stages.Stage>,
  +tree: Finite.Table(Directory.width(name), Solver.Node<Directory.width(name)>), +key: Word(Directory.width(name)),
  +previous: Finite.Table(Directory.width(name), Game.Outcome),
  built: {Compile.graph(name, stage, stages) == Some{tree} : Maybe<&2, Finite.Table(Directory.width(name), Solver.Node<Directory.width(name)>)>}) ->
  {Some{Finite.get(Directory.width(name), Game.Outcome, key, Solver.layer(Directory.width(name), tree, Solver.Next{previous}))} ==
    node_value(Directory.width(name), Compile.entry(name, stage, stages, key), previous) : Maybe<&2, Game.Outcome>}:
  %Equal.sym(Maybe<&2, Solver.Node<Directory.width(name)>>, Compile.entry(name, stage, stages, key),
    Some{Finite.get(Directory.width(name), Solver.Node<Directory.width(name)>, key, tree)}, graph(name, stage, stages, tree, key, built)) :
    {Some{Finite.get(Directory.width(name), Game.Outcome, key, Solver.layer(Directory.width(name), tree, Solver.Next{previous}))} ==
      node_value(Directory.width(name), _, previous) : Maybe<&2, Game.Outcome>}
  Equal.cong(Game.Outcome, Maybe<&2, Game.Outcome>, result => Some{result},
    Finite.get(Directory.width(name), Game.Outcome, key, Solver.layer(Directory.width(name), tree, Solver.Next{previous})),
    Solver.at(Directory.width(name), Solver.Next{previous}, Finite.get(Directory.width(name), Solver.Node<Directory.width(name)>, key, tree)),
    SolverProof.lookup(Directory.width(name), tree, Solver.Next{previous}, key))
