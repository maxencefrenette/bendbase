import Base
import ./game.bend as Game

def choice_sound(+player: Game.Player, +turn: Game.Player,
  +left: Game.Outcome, +right: Game.Outcome,
  yes: Game.Truth(Game.wins(player, Game.best(turn, left, right)))) ->
  Game.EitherOrBoth(player, turn,
    Game.Truth(Game.wins(player, left)), Game.Truth(Game.wins(player, right))):
  match player turn left right:
    case Game.White{} Game.White{} Game.WhiteWin{} Game.WhiteWin{}:
      Inl{Unit{}}
    case Game.White{} Game.White{} Game.WhiteWin{} Game.Draw{}:
      Inl{Unit{}}
    case Game.White{} Game.White{} Game.WhiteWin{} Game.BlackWin{}:
      Inl{Unit{}}
    case Game.White{} Game.White{} Game.Draw{} Game.WhiteWin{}:
      Inr{Unit{}}
    case Game.White{} Game.White{} Game.Draw{} Game.Draw{}:
      match yes:
    case Game.White{} Game.White{} Game.Draw{} Game.BlackWin{}:
      match yes:
    case Game.White{} Game.White{} Game.BlackWin{} Game.WhiteWin{}:
      Inr{Unit{}}
    case Game.White{} Game.White{} Game.BlackWin{} Game.Draw{}:
      match yes:
    case Game.White{} Game.White{} Game.BlackWin{} Game.BlackWin{}:
      match yes:
    case Game.White{} Game.Black{} Game.WhiteWin{} Game.WhiteWin{}:
      (Unit{}, Unit{})
    case Game.White{} Game.Black{} Game.WhiteWin{} Game.Draw{}:
      match yes:
    case Game.White{} Game.Black{} Game.WhiteWin{} Game.BlackWin{}:
      match yes:
    case Game.White{} Game.Black{} Game.Draw{} Game.WhiteWin{}:
      match yes:
    case Game.White{} Game.Black{} Game.Draw{} Game.Draw{}:
      match yes:
    case Game.White{} Game.Black{} Game.Draw{} Game.BlackWin{}:
      match yes:
    case Game.White{} Game.Black{} Game.BlackWin{} Game.WhiteWin{}:
      match yes:
    case Game.White{} Game.Black{} Game.BlackWin{} Game.Draw{}:
      match yes:
    case Game.White{} Game.Black{} Game.BlackWin{} Game.BlackWin{}:
      match yes:
    case Game.Black{} Game.White{} Game.WhiteWin{} Game.WhiteWin{}:
      match yes:
    case Game.Black{} Game.White{} Game.WhiteWin{} Game.Draw{}:
      match yes:
    case Game.Black{} Game.White{} Game.WhiteWin{} Game.BlackWin{}:
      match yes:
    case Game.Black{} Game.White{} Game.Draw{} Game.WhiteWin{}:
      match yes:
    case Game.Black{} Game.White{} Game.Draw{} Game.Draw{}:
      match yes:
    case Game.Black{} Game.White{} Game.Draw{} Game.BlackWin{}:
      match yes:
    case Game.Black{} Game.White{} Game.BlackWin{} Game.WhiteWin{}:
      match yes:
    case Game.Black{} Game.White{} Game.BlackWin{} Game.Draw{}:
      match yes:
    case Game.Black{} Game.White{} Game.BlackWin{} Game.BlackWin{}:
      (Unit{}, Unit{})
    case Game.Black{} Game.Black{} Game.WhiteWin{} Game.WhiteWin{}:
      match yes:
    case Game.Black{} Game.Black{} Game.WhiteWin{} Game.Draw{}:
      match yes:
    case Game.Black{} Game.Black{} Game.WhiteWin{} Game.BlackWin{}:
      Inr{Unit{}}
    case Game.Black{} Game.Black{} Game.Draw{} Game.WhiteWin{}:
      match yes:
    case Game.Black{} Game.Black{} Game.Draw{} Game.Draw{}:
      match yes:
    case Game.Black{} Game.Black{} Game.Draw{} Game.BlackWin{}:
      Inr{Unit{}}
    case Game.Black{} Game.Black{} Game.BlackWin{} Game.WhiteWin{}:
      Inl{Unit{}}
    case Game.Black{} Game.Black{} Game.BlackWin{} Game.Draw{}:
      Inl{Unit{}}
    case Game.Black{} Game.Black{} Game.BlackWin{} Game.BlackWin{}:
      Inl{Unit{}}

def choice_complete(+player: Game.Player, +turn: Game.Player,
  +left: Game.Outcome, +right: Game.Outcome,
  evidence: Game.EitherOrBoth(player, turn,
    Game.Truth(Game.wins(player, left)), Game.Truth(Game.wins(player, right)))) ->
  Game.Truth(Game.wins(player, Game.best(turn, left, right))):
  match player turn left right:
    case Game.White{} Game.White{} Game.WhiteWin{} Game.WhiteWin{}:
      Unit{}
    case Game.White{} Game.White{} Game.WhiteWin{} Game.Draw{}:
      Unit{}
    case Game.White{} Game.White{} Game.WhiteWin{} Game.BlackWin{}:
      Unit{}
    case Game.White{} Game.White{} Game.Draw{} Game.WhiteWin{}:
      Unit{}
    case Game.White{} Game.White{} Game.Draw{} Game.Draw{}:
      match evidence:
        case Inl{bad}:
          bad
        case Inr{bad}:
          bad
    case Game.White{} Game.White{} Game.Draw{} Game.BlackWin{}:
      match evidence:
        case Inl{bad}:
          bad
        case Inr{bad}:
          bad
    case Game.White{} Game.White{} Game.BlackWin{} Game.WhiteWin{}:
      Unit{}
    case Game.White{} Game.White{} Game.BlackWin{} Game.Draw{}:
      match evidence:
        case Inl{bad}:
          bad
        case Inr{bad}:
          bad
    case Game.White{} Game.White{} Game.BlackWin{} Game.BlackWin{}:
      match evidence:
        case Inl{bad}:
          bad
        case Inr{bad}:
          bad
    case Game.White{} Game.Black{} Game.WhiteWin{} Game.WhiteWin{}:
      Unit{}
    case Game.White{} Game.Black{} Game.WhiteWin{} Game.Draw{}:
      match evidence:
        case Tuple{a, b}:
          b
    case Game.White{} Game.Black{} Game.WhiteWin{} Game.BlackWin{}:
      match evidence:
        case Tuple{a, b}:
          b
    case Game.White{} Game.Black{} Game.Draw{} Game.WhiteWin{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.White{} Game.Black{} Game.Draw{} Game.Draw{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.White{} Game.Black{} Game.Draw{} Game.BlackWin{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.White{} Game.Black{} Game.BlackWin{} Game.WhiteWin{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.White{} Game.Black{} Game.BlackWin{} Game.Draw{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.White{} Game.Black{} Game.BlackWin{} Game.BlackWin{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.Black{} Game.White{} Game.WhiteWin{} Game.WhiteWin{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.Black{} Game.White{} Game.WhiteWin{} Game.Draw{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.Black{} Game.White{} Game.WhiteWin{} Game.BlackWin{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.Black{} Game.White{} Game.Draw{} Game.WhiteWin{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.Black{} Game.White{} Game.Draw{} Game.Draw{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.Black{} Game.White{} Game.Draw{} Game.BlackWin{}:
      match evidence:
        case Tuple{a, b}:
          a
    case Game.Black{} Game.White{} Game.BlackWin{} Game.WhiteWin{}:
      match evidence:
        case Tuple{a, b}:
          b
    case Game.Black{} Game.White{} Game.BlackWin{} Game.Draw{}:
      match evidence:
        case Tuple{a, b}:
          b
    case Game.Black{} Game.White{} Game.BlackWin{} Game.BlackWin{}:
      Unit{}
    case Game.Black{} Game.Black{} Game.WhiteWin{} Game.WhiteWin{}:
      match evidence:
        case Inl{bad}:
          bad
        case Inr{bad}:
          bad
    case Game.Black{} Game.Black{} Game.WhiteWin{} Game.Draw{}:
      match evidence:
        case Inl{bad}:
          bad
        case Inr{bad}:
          bad
    case Game.Black{} Game.Black{} Game.WhiteWin{} Game.BlackWin{}:
      Unit{}
    case Game.Black{} Game.Black{} Game.Draw{} Game.WhiteWin{}:
      match evidence:
        case Inl{bad}:
          bad
        case Inr{bad}:
          bad
    case Game.Black{} Game.Black{} Game.Draw{} Game.Draw{}:
      match evidence:
        case Inl{bad}:
          bad
        case Inr{bad}:
          bad
    case Game.Black{} Game.Black{} Game.Draw{} Game.BlackWin{}:
      Unit{}
    case Game.Black{} Game.Black{} Game.BlackWin{} Game.WhiteWin{}:
      Unit{}
    case Game.Black{} Game.Black{} Game.BlackWin{} Game.Draw{}:
      Unit{}
    case Game.Black{} Game.Black{} Game.BlackWin{} Game.BlackWin{}:
      Unit{}

def or_map(-A: Type, -B: Type, -C: Type, -D: Type,
  evidence: A | B, f: A -> C, g: B -> D) -> C | D:
  match evidence:
    case Inl{a}:
      Inl{f(a)}
    case Inr{b}:
      Inr{g(b)}

def and_map(-A: Type, -B: Type, -C: Type, -D: Type,
  evidence: A & B, f: A -> C, g: B -> D) -> C & D:
  match evidence:
    case Tuple{a, b}:
      (f(a), g(b))

def sound(+tree: Game.Tree, +player: Game.Player,
  yes: Game.Truth(Game.wins(player, Game.evaluate(tree)))) -> Game.Forces(player, tree):
  match tree player:
    case Game.End{result} Game.White{}:
      yes
    case Game.End{result} Game.Black{}:
      yes
    case Game.Choose{Game.White{}, +left, +right} Game.White{}:
      or_map(
        Game.Truth(Game.wins(Game.White{}, Game.evaluate(left))),
        Game.Truth(Game.wins(Game.White{}, Game.evaluate(right))),
        Game.Forces(Game.White{}, left), Game.Forces(Game.White{}, right),
        choice_sound(Game.White{}, Game.White{}, Game.evaluate(left), Game.evaluate(right), yes),
        a => sound(left, Game.White{}, a),
        b => sound(right, Game.White{}, b))
    case Game.Choose{Game.Black{}, +left, +right} Game.White{}:
      and_map(
        Game.Truth(Game.wins(Game.White{}, Game.evaluate(left))),
        Game.Truth(Game.wins(Game.White{}, Game.evaluate(right))),
        Game.Forces(Game.White{}, left), Game.Forces(Game.White{}, right),
        choice_sound(Game.White{}, Game.Black{}, Game.evaluate(left), Game.evaluate(right), yes),
        a => sound(left, Game.White{}, a),
        b => sound(right, Game.White{}, b))
    case Game.Choose{Game.White{}, +left, +right} Game.Black{}:
      and_map(
        Game.Truth(Game.wins(Game.Black{}, Game.evaluate(left))),
        Game.Truth(Game.wins(Game.Black{}, Game.evaluate(right))),
        Game.Forces(Game.Black{}, left), Game.Forces(Game.Black{}, right),
        choice_sound(Game.Black{}, Game.White{}, Game.evaluate(left), Game.evaluate(right), yes),
        a => sound(left, Game.Black{}, a),
        b => sound(right, Game.Black{}, b))
    case Game.Choose{Game.Black{}, +left, +right} Game.Black{}:
      or_map(
        Game.Truth(Game.wins(Game.Black{}, Game.evaluate(left))),
        Game.Truth(Game.wins(Game.Black{}, Game.evaluate(right))),
        Game.Forces(Game.Black{}, left), Game.Forces(Game.Black{}, right),
        choice_sound(Game.Black{}, Game.Black{}, Game.evaluate(left), Game.evaluate(right), yes),
        a => sound(left, Game.Black{}, a),
        b => sound(right, Game.Black{}, b))

def complete(+tree: Game.Tree, +player: Game.Player,
  evidence: Game.Forces(player, tree)) -> Game.Truth(Game.wins(player, Game.evaluate(tree))):
  match tree player:
    case Game.End{result} Game.White{}:
      evidence
    case Game.End{result} Game.Black{}:
      evidence
    case Game.Choose{Game.White{}, +left, +right} Game.White{}:
      choice_complete(Game.White{}, Game.White{}, Game.evaluate(left), Game.evaluate(right),
        or_map(
          Game.Forces(Game.White{}, left), Game.Forces(Game.White{}, right),
          Game.Truth(Game.wins(Game.White{}, Game.evaluate(left))),
          Game.Truth(Game.wins(Game.White{}, Game.evaluate(right))),
          evidence,
          a => complete(left, Game.White{}, a),
          b => complete(right, Game.White{}, b)))
    case Game.Choose{Game.Black{}, +left, +right} Game.White{}:
      choice_complete(Game.White{}, Game.Black{}, Game.evaluate(left), Game.evaluate(right),
        and_map(
          Game.Forces(Game.White{}, left), Game.Forces(Game.White{}, right),
          Game.Truth(Game.wins(Game.White{}, Game.evaluate(left))),
          Game.Truth(Game.wins(Game.White{}, Game.evaluate(right))),
          evidence,
          a => complete(left, Game.White{}, a),
          b => complete(right, Game.White{}, b)))
    case Game.Choose{Game.White{}, +left, +right} Game.Black{}:
      choice_complete(Game.Black{}, Game.White{}, Game.evaluate(left), Game.evaluate(right),
        and_map(
          Game.Forces(Game.Black{}, left), Game.Forces(Game.Black{}, right),
          Game.Truth(Game.wins(Game.Black{}, Game.evaluate(left))),
          Game.Truth(Game.wins(Game.Black{}, Game.evaluate(right))),
          evidence,
          a => complete(left, Game.Black{}, a),
          b => complete(right, Game.Black{}, b)))
    case Game.Choose{Game.Black{}, +left, +right} Game.Black{}:
      choice_complete(Game.Black{}, Game.Black{}, Game.evaluate(left), Game.evaluate(right),
        or_map(
          Game.Forces(Game.Black{}, left), Game.Forces(Game.Black{}, right),
          Game.Truth(Game.wins(Game.Black{}, Game.evaluate(left))),
          Game.Truth(Game.wins(Game.Black{}, Game.evaluate(right))),
          evidence,
          a => complete(left, Game.Black{}, a),
          b => complete(right, Game.Black{}, b)))
