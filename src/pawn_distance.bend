import Base
import ./game.bend as Game

# Squares are rank bits followed by file bits, both most significant first.
# Thus this is 7-rank for White and rank for Black, including both back ranks.
def digit(owner: Game.Player, bit: Bool) -> Bool:
  match owner:
    case Game.White{}:
      Bool.not(bit)
    case Game.Black{}:
      bit

def distance(+owner: Game.Player, square: Word(6n)) -> Nat:
  match square:
    case WCon{a, WCon{b, WCon{c, file}}}:
      Nat.add(Bool.pick(Nat, digit(owner, a), 4n, 0n),
        Nat.add(Bool.pick(Nat, digit(owner, b), 2n, 0n), Bool.pick(Nat, digit(owner, c), 1n, 0n)))

# Exact forward rank displacement; file movement is checked separately.
def forward(+owner: Game.Player, from: Word(6n), dest: Word(6n), steps: Nat) -> Bool:
  Nat.is_eq(distance(owner, from), Nat.add(steps, distance(owner, dest)))
