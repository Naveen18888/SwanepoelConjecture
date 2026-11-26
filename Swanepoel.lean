module
public import Swanepoel.Geometry
public import Swanepoel.Sharpness
public import Swanepoel.L38Progress
@[expose] public section

namespace Swanepoel

theorem swanepoel : SwanepoelConjecture := ⟨upper_bound, sharpness⟩

theorem maximum_edges (n : ℕ) (hn : 1 ≤ n) :
    (∀ G : PennyGraph n, G.TriangleFree → (G.edgeCount : ℤ) ≤ extremalValue n) ∧
    (∃ G : PennyGraph n, G.TriangleFree ∧ (G.edgeCount : ℤ) = extremalValue n) :=
  ⟨upper_bound n hn, sharpness n hn⟩

end Swanepoel
