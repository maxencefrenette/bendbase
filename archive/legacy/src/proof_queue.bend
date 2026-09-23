import Base
import ./rules.bend as Rules

# A persistent FIFO queue. Both lists are Data, so queue invariants can refer
# to the same logical queue before and after an operation without affine forks.
type Queue is Data:
  Queue{front: List<&2, Rules.State>, back: List<&2, Rules.State>}

def new() -> Queue:
  Queue{Nil{}, Nil{}}

def push(queue: Queue, state: Rules.State) -> Queue:
  match queue:
    case Queue{front, back}:
      Queue{front, state <> back}

def pop_front(front: List<&2, Rules.State>,
  back: List<&2, Rules.State>) -> Queue & Maybe<&2, Rules.State>:
  match front:
    case Nil{}:
      (Queue{Nil{}, back}, None{})
    case head <> rest:
      (Queue{rest, back}, Some{head})

def pop(queue: Queue) -> Queue & Maybe<&2, Rules.State>:
  match queue:
    case Queue{front, back}:
      match front:
        case Nil{}:
          pop_front(List.reverse(&2, Rules.State, back), Nil{})
        case head <> rest:
          (Queue{rest, back}, Some{head})

def contents(queue: Queue) -> List<&2, Rules.State>:
  match queue:
    case Queue{front, back}:
      match back:
        case Nil{}:
          front
        case head <> rest:
          List.append(&2, Rules.State, front,
            List.reverse(&2, Rules.State, head <> rest))

def reassemble(read: Queue & Maybe<&2, Rules.State>) ->
  List<&2, Rules.State>:
  match read:
    case (queue, None{}):
      contents(queue)
    case (queue, Some{state}):
      state <> contents(queue)
