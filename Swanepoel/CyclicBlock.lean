module
public import Swanepoel.ConnectedBounds
@[expose] public section
set_option autoImplicit false

namespace Swanepoel

def PennyGraph.CyclicBlock {n : ℕ} (G : PennyGraph n) : Prop :=
  3≤n ∧ G.graph.Connected ∧
    ∀ v : Fin n,(G.graph.induce {w | w≠v}).Connected

end Swanepoel
