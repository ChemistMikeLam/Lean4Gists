module

namespace Lean4Gists.Misc

public def ackermann : Nat → Nat → Nat
  | 0, n => n + 1
  | (m + 1), 0 => ackermann m 1
  | (m + 1), (n + 1) => ackermann m $ ackermann (m + 1) n

end Lean4Gists.Misc

