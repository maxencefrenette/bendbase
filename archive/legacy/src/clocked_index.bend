import Base
import ./encoding.bend as Encoding

# A structural index path. A Word stores its least significant bit first;
# ProofTree follows the most significant index bit first. Reversal relates
# the two without numeric reconstruction or a scan of table indices.
def snoc(n: Nat, +word: Word(n), +bit: Bool) ->
  Word(1n+n):
  match n word:
    case 0n WNil{}:
      WCon{bit, WNil{}}
    case 1n+rest WCon{head, tail}:
      WCon{head, snoc(rest, tail, bit)}

def reverse(n: Nat, word: Word(n)) -> Word(n):
  match n word:
    case 0n WNil{}:
      WNil{}
    case 1n++rest WCon{head, tail}:
      snoc(rest, reverse(rest, tail), head)

def low19.fin(pair: Word(19n) & Word(13n)) ->
  Word(19n):
  match pair:
    case (low, high):
      low

def low19(index: U32) -> Word(19n):
  match index:
    case U32{word}:
      low19.fin(Encoding.split(13n, 19n, word))

def path(index: U32) -> Word(19n):
  reverse(19n, low19(index))
