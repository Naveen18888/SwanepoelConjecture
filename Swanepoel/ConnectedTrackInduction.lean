module
public import Swanepoel.CutHighCrossingCap
public import Swanepoel.BlockTrackLeafGraph
@[expose] public section
set_option autoImplicit false

noncomputable section
namespace Swanepoel

theorem connected_disjoint_bounds_of_leaf_transport
    (leafStep : ∀ n : ℕ,∀ G : PennyGraph n,∀ ht : G.TriangleFree,
      G.graph.Connected → ∀ v a : Fin n,G.graph.Adj v a →
        (∀ b,G.graph.Adj v b → b=a) →
        (componentSystem (G.eraseVertex v) (G.eraseVertex_triangleFree ht v)
          (G.eraseVertex v).ordinaryTrackComponents
          ((G.eraseVertex v).faceDefectCount (G.eraseVertex_triangleFree ht v))).DisjointBound →
        (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).DisjointBound) :
    ∀ n : ℕ,∀ G : PennyGraph n,∀ ht : G.TriangleFree,G.graph.Connected →
      (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).DisjointBound := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G ht hc
    by_cases hd : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a
    · exact G.disjoint_bound_of_min_degree_and_smaller_bounds ht hc hd ih
    · push Not at hd
      obtain ⟨v,a,hva,hunique⟩ := hd
      apply leafStep n G ht hc v a hva hunique
      exact ih _ (G.eraseVertex_card_lt v) (G.eraseVertex v)
        (G.eraseVertex_triangleFree ht v) (G.eraseVertex_connected hc v a hva hunique)

end Swanepoel
