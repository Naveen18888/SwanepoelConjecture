module
public import Swanepoel.FacePortLowerBound
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem physicalEdge_unordered {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    s((physicalEdge e).val.1,(physicalEdge e).val.2) = s(e.val.1,e.val.2) := by
  by_cases h : e.val.1 < e.val.2
  · simp [physicalEdge, h]
  · simp only [physicalEdge, dite_eq_right h]
    exact Sym2.eq_swap

theorem PennyGraph.defect_port_graph_not_isAcyclic {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    ¬ (G.contactGraph (G.facePortEdges F)).IsAcyclic := by
  intro ha
  exact (G.defect_face_retained_by_source_edges ht F hF).not_isBounded_of_acyclic ha
    (G.defectPlaneFace_isBounded ht hF)

theorem PennyGraph.defect_exists_selected_port_cycle {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    ∃ a : Fin n, ∃ p : (G.contactGraph (G.facePortEdges F)).Walk a a,
      p.IsCycle ∧ 4 ≤ p.length := by
  have hnot := G.defect_port_graph_not_isAcyclic ht F hF
  have hex : ∃ a : Fin n, ∃ p : (G.contactGraph (G.facePortEdges F)).Walk a a, p.IsCycle := by
    by_contra hn
    apply hnot
    intro a p hp
    exact hn ⟨a,p,hp⟩
  obtain ⟨a,p,hp⟩ := hex
  refine ⟨a,p,hp,?_⟩
  apply triangle_free_cycle_four_le _ _ p hp
  intro a b c hab hbc hca
  exact ht a b c (G.contactGraph_le _ hab) (G.contactGraph_le _ hbc) (G.contactGraph_le _ hca)

theorem PennyGraph.port_graph_edge_has_source_orientation {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) {a b : Fin n}
    (hab : (G.contactGraph (G.facePortEdges F)).Adj a b) :
    ∃ e ∈ G.faceSourcePorts F, s(e.val.1,e.val.2) = s(a,b) := by
  obtain ⟨e,he,heab⟩ := hab
  obtain ⟨port,hport,hphysical⟩ := Finset.mem_image.mp he
  refine ⟨port,hport,?_⟩
  calc
    _ = s((physicalEdge port).val.1,(physicalEdge port).val.2) := (physicalEdge_unordered port).symm
    _ = s(e.val.1,e.val.2) := by rw [hphysical]
    _ = _ := heab

theorem PennyGraph.defect_exists_original_port_cycle {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    ∃ a : Fin n, ∃ p : G.graph.Walk a a, p.IsCycle ∧ 4 ≤ p.length ∧
      ∀ z ∈ p.edges, ∃ e ∈ G.faceSourcePorts F, s(e.val.1,e.val.2) = z := by
  obtain ⟨a,p,hp,hlen⟩ := G.defect_exists_selected_port_cycle ht F hF
  let hle := G.contactGraph_le (G.facePortEdges F)
  refine ⟨a,p.mapLe hle,hp.mapLe hle,?_,?_⟩
  · simpa only [SimpleGraph.Walk.length_mapLe] using hlen
  · intro z hz
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hz
    have hzedge := p.edges_subset_edgeSet hz
    induction z using Sym2.inductionOn with
    | _ i j =>
      exact G.port_graph_edge_has_source_orientation F hzedge

structure FacePortCycle {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) where
  length : ℕ
  four_le_length : 4 ≤ length
  vertex : Fin (length+1) → Fin n
  closes : vertex 0 = vertex (Fin.last length)
  vertex_injective : Function.Injective (fun i : Fin length => vertex i.castSucc)
  contact : ∀ i : Fin length, G.graph.Adj (vertex i.castSucc) (vertex i.succ)
  port : Fin length → OrientedEdge G
  port_source : ∀ i, SpineSource (port i)
  port_face : ∀ i, G.sourceFace (port i) = F
  port_side : ∀ i, s((port i).val.1,(port i).val.2) = s(vertex i.castSucc,vertex i.succ)

theorem PennyGraph.defect_facePortCycle {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    Nonempty (FacePortCycle G F) := by
  obtain ⟨a,p,hp,hlen⟩ := G.defect_exists_selected_port_cycle ht F hF
  have hex (i : Fin p.length) : ∃ e ∈ G.faceSourcePorts F,
      s(e.val.1,e.val.2) = s(p.getVert i.val,p.getVert (i.val+1)) :=
    G.port_graph_edge_has_source_orientation F (p.adj_getVert_succ i.isLt)
  choose port hport hside using hex
  refine ⟨{
    length := p.length
    four_le_length := hlen
    vertex := fun i => p.getVert i.val
    closes := by simp
    vertex_injective := ?_
    contact := fun i => G.contactGraph_le _ (p.adj_getVert_succ i.isLt)
    port := port
    port_source := fun i => (Finset.mem_filter.mp (hport i)).2.1
    port_face := fun i => (Finset.mem_filter.mp (hport i)).2.2
    port_side := hside
  }⟩
  intro i j hij
  apply Fin.ext
  exact hp.getVert_injOn' (by change i.val ≤ p.length-1; omega)
    (by change j.val ≤ p.length-1; omega) hij

end Swanepoel
