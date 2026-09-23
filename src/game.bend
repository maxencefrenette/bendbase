import Base

# An ordinary finite perfect-information game. Choice nodes are nonempty;
# chess stalemate and checkmate are represented explicitly by End nodes.
type Player is Data:
  White{}
  Black{}

type Outcome is Data:
  WhiteWin{}
  Draw{}
  BlackWin{}

type Tree is Data:
  End{result: Outcome}
  Choose{turn: Player, left: Tree, right: Tree}

def Truth(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def wins(player: Player, result: Outcome) -> Bool:
  match player result:
    case White{} WhiteWin{}:
      True{}
    case Black{} BlackWin{}:
      True{}
    case _ _:
      False{}

# A strategy chooses a continuation on its own turn and must handle BOTH
# continuations on its opponent's turn. No evaluator appears in this type.
def Forces(+player: Player, tree: Tree) -> Type:
  match player tree:
    case White{} End{result}:
      Truth(wins(White{}, result))
    case Black{} End{result}:
      Truth(wins(Black{}, result))
    case White{} Choose{White{}, left, right}:
      Forces(White{}, left) | Forces(White{}, right)
    case Black{} Choose{Black{}, left, right}:
      Forces(Black{}, left) | Forces(Black{}, right)
    case White{} Choose{Black{}, left, right}:
      Forces(White{}, left) & Forces(White{}, right)
    case Black{} Choose{White{}, left, right}:
      Forces(Black{}, left) & Forces(Black{}, right)

def best(turn: Player, left: Outcome, right: Outcome) -> Outcome:
  match turn left right:
    case White{} WhiteWin{} _:
      WhiteWin{}
    case White{} _ WhiteWin{}:
      WhiteWin{}
    case White{} Draw{} _:
      Draw{}
    case White{} _ Draw{}:
      Draw{}
    case White{} BlackWin{} BlackWin{}:
      BlackWin{}
    case Black{} BlackWin{} _:
      BlackWin{}
    case Black{} _ BlackWin{}:
      BlackWin{}
    case Black{} Draw{} _:
      Draw{}
    case Black{} _ Draw{}:
      Draw{}
    case Black{} WhiteWin{} WhiteWin{}:
      WhiteWin{}

def evaluate(tree: Tree) -> Outcome:
  match tree:
    case End{result}:
      result
    case Choose{turn, left, right}:
      best(turn, evaluate(left), evaluate(right))

# Signed WDL encoded as one byte: 1 = White win, 0 = draw, 255 = -1.
def byte(result: Outcome) -> U32:
  match result:
    case WhiteWin{}:
      1
    case Draw{}:
      0
    case BlackWin{}:
      255

def EitherOrBoth(player: Player, turn: Player,
  -A: Type, -B: Type) -> Type:
  match player turn:
    case White{} White{}:
      A | B
    case Black{} Black{}:
      A | B
    case _ _:
      A & B

# Exact, two-directional WDL semantics for a stored byte. For Draw neither
# player has a forcing strategy; for either winning value that player does.
def CorrectByte(+tree: Tree, stored: Maybe<&2, U32>) -> Type:
  &outcome: Outcome ->
    {stored == Some{byte(outcome)} : Maybe<&2, U32>} &
    (@player: Player ->
      ((Truth(wins(player, outcome)) -> Forces(player, tree)) &
       (Forces(player, tree) -> Truth(wins(player, outcome)))))
