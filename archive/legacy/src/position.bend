import Base

# A square is an integer from 0 (a1) through 63 (h8).
def distance(+a: U32, +b: U32) -> U32:
  (U32.max(a, b) - U32.min(a, b) : U32)

def kings_touch(+white_king: U32, +black_king: U32) -> Bool:
  file_distance = distance((white_king % 8 : U32), (black_king % 8 : U32))
  rank_distance = distance((white_king / 8 : U32), (black_king / 8 : U32))
  U32.is_le(file_distance, 1) && U32.is_le(rank_distance, 1)
