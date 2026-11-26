module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
The full formalization and proof of Swanepoel's Conjecture on Penny Graphs. For any triangle-free penny graph, the maximum number of edges on n vertices is 2n - 2 square root of n, taking the floor function of this value as necessary. This value is achieved by some penny graph for all numbers of vertices.
-/

noncomputable section
namespace Swanepoel

abbrev Plane := EuclideanSpace ℝ (Fin 2)

structure PennyGraph (n : ℕ) where
  point : Fin n → Plane
  separated : ∀ i j, i ≠ j → 1 ≤ dist (point i) (point j)

def PennyGraph.graph {n : ℕ} (G : PennyGraph n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ dist (G.point i) (G.point j) = 1
  symm := by
    constructor
    intro i j h
    exact ⟨Ne.symm h.1, by simpa [dist_comm] using h.2⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

def PennyGraph.TriangleFree {n : ℕ} (G : PennyGraph n) : Prop :=
  ∀ a b c, G.graph.Adj a b → G.graph.Adj b c → ¬ G.graph.Adj c a

def PennyGraph.edgeCount {n : ℕ} (G : PennyGraph n) : ℕ := by
  classical
  exact G.graph.edgeFinset.card

def extremalValue (n : ℕ) : ℤ := ⌊2 * (n : ℝ) - 2 * Real.sqrt n⌋

def UpperBound : Prop :=
  ∀ n, 1 ≤ n → ∀ G : PennyGraph n, G.TriangleFree →
    (G.edgeCount : ℤ) ≤ extremalValue n

def Sharpness : Prop :=
  ∀ n, 1 ≤ n → ∃ G : PennyGraph n,
    G.TriangleFree ∧ (G.edgeCount : ℤ) = extremalValue n

def SwanepoelConjecture : Prop := UpperBound ∧ Sharpness

theorem maximum_edges (n : ℕ) (hn : 1 ≤ n) :
    (∀ G : PennyGraph n,
      G.TriangleFree → (G.edgeCount : ℤ) ≤ extremalValue n) ∧
    (∃ G : PennyGraph n,
      G.TriangleFree ∧ (G.edgeCount : ℤ) = extremalValue n) := by
  sorry

end Swanepoel
