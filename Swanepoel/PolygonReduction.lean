module
public import Swanepoel.CycleSeparation
public import Swanepoel.EulerForest
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.selectedWalkEdges {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) {a b : Fin n} (p : (G.contactGraph S).Walk a b) :
    Finset (ContactEdge G) := S.filter (fun e => s(e.val.1,e.val.2)∈p.edges)

theorem PennyGraph.selectedWalkEdges_subset {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) {a b : Fin n} (p : (G.contactGraph S).Walk a b) :
    G.selectedWalkEdges S p⊆S := Finset.filter_subset _ _

theorem PennyGraph.walk_edges_mem_selectedWalkEdges {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) {a b : Fin n} (p : (G.contactGraph S).Walk a b) :
    ∀ z, z∈p.edges → z∈(G.contactGraph (G.selectedWalkEdges S p)).edgeSet := by
  intro z hz
  induction z using Sym2.inductionOn with
  | _ i j =>
    obtain ⟨e,he,heq⟩ := p.adj_of_mem_edges hz
    refine ⟨e,Finset.mem_filter.mpr ⟨he,?_⟩,heq⟩
    rwa [heq]

def PennyGraph.selectedWalk {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) {a b : Fin n} (p : (G.contactGraph S).Walk a b) :
    (G.contactGraph (G.selectedWalkEdges S p)).Walk a b :=
  p.transfer _ (G.walk_edges_mem_selectedWalkEdges S p)

theorem PennyGraph.selectedWalk_isPath {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) {a b : Fin n} (p : (G.contactGraph S).Walk a b)
    (hp : p.IsPath) : (G.selectedWalk S p).IsPath := hp.transfer _

theorem PennyGraph.selectedWalkEdges_selectedWalk {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) {a b : Fin n} (p : (G.contactGraph S).Walk a b) :
    G.selectedWalkEdges (G.selectedWalkEdges S p) (G.selectedWalk S p)=
      G.selectedWalkEdges S p := by
  change (G.selectedWalkEdges S p).filter
    (fun e => s(e.val.1,e.val.2)∈(G.selectedWalk S p).edges)=G.selectedWalkEdges S p
  apply Finset.filter_eq_self.mpr
  intro e he
  change s(e.val.1,e.val.2)∈(p.transfer _ (G.walk_edges_mem_selectedWalkEdges S p)).edges
  rw [SimpleGraph.Walk.edges_transfer]
  exact (Finset.mem_filter.mp he).2

theorem PennyGraph.faceEuler_of_simple_path_separation {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected)
    (hpolygon : ∀ P : Finset (ContactEdge G), ∀ e : ContactEdge G, e∉P →
      ∀ p : (G.contactGraph P).Walk e.val.1 e.val.2, p.IsPath →
      G.selectedWalkEdges P p=P → ¬G.SameInsertionSides P e) : G.FaceEuler := by
  apply G.faceEuler_of_cycle_separation hc
  intro S e he hr
  obtain ⟨p,hp⟩ := hr.exists_isPath
  have hsub := G.selectedWalkEdges_subset S p
  apply G.separateInsertionSides_mono hsub e he
  exact hpolygon (G.selectedWalkEdges S p) e (fun h => he (hsub h))
    (G.selectedWalk S p) (G.selectedWalk_isPath S p hp) (G.selectedWalkEdges_selectedWalk S p)

theorem PennyGraph.euler_with_defects_of_simple_path_separation {n : ℕ}
    (G : PennyGraph n) (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hpolygon : ∀ P : Finset (ContactEdge G), ∀ e : ContactEdge G, e∉P →
      ∀ p : (G.contactGraph P).Walk e.val.1 e.val.2, p.IsPath →
      G.selectedWalkEdges P p=P → ¬G.SameInsertionSides P e) :
    (n : ℤ)-G.edgeCount+(Fintype.card (RhombusSet G)+G.faceDefectCount ht)=1 :=
  G.euler_with_defects ht (G.faceEuler_of_simple_path_separation hc hpolygon)

end Swanepoel
