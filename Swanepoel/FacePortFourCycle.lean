module
public import Swanepoel.FacePortCycles
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.four_port_edges_rhombus_endpoints {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht)
    (hsmall : (G.facePortEdges F).card ≤ 4) :
    ∃ C : RhombusCell G, ∀ e ∈ G.facePortEdges F,
      e.val.1 ∈ C.corners ∧ e.val.2 ∈ C.corners := by
  obtain ⟨a,p,hp,hfour⟩ := G.defect_exists_selected_port_cycle ht F hF
  have hupper := cycle_length_le_edge_count (G.contactGraph (G.facePortEdges F)) p hp
  rw [G.contactGraph_edge_count] at hupper
  have hlen : p.length = 4 := by omega
  have hget (i j : ℕ) (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
      p.getVert i ≠ p.getVert j := by
    intro heq
    apply hij
    exact hp.getVert_injOn' (by change i ≤ p.length-1; omega)
      (by change j ≤ p.length-1; omega) heq
  have hp4 : p.getVert 4 = p.getVert 0 := by
    rw [← hlen, p.getVert_length, p.getVert_zero]
  let C : RhombusCell G := {
    a := p.getVert 0
    b := p.getVert 1
    c := p.getVert 2
    d := p.getVert 3
    ac := hget 0 2 (by omega) (by omega) (by omega)
    bd := hget 1 3 (by omega) (by omega) (by omega)
    ab := G.contactGraph_le _ (p.adj_getVert_succ (i := 0) (by omega))
    bc := G.contactGraph_le _ (p.adj_getVert_succ (i := 1) (by omega))
    cd := G.contactGraph_le _ (p.adj_getVert_succ (i := 2) (by omega))
    da := by
      have ha := G.contactGraph_le _ (p.adj_getVert_succ (i := 3) (by omega))
      simpa only [hp4] using ha
  }
  have hcard : p.edges.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup hp.edges_nodup, p.length_edges, hlen]
  have hsubset : p.edges.toFinset ⊆ (G.contactGraph (G.facePortEdges F)).edgeFinset := by
    intro z hz
    exact SimpleGraph.mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp hz))
  have heq : p.edges.toFinset = (G.contactGraph (G.facePortEdges F)).edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hcard, G.contactGraph_edge_count]; exact hsmall)
  refine ⟨C, ?_⟩
  intro e he
  have hem : s(e.val.1,e.val.2) ∈ p.edges := by
    apply List.mem_toFinset.mp
    rw [heq]
    exact SimpleGraph.mem_edgeFinset.mpr ((G.contactGraph_adj_iff _ e).mpr he)
  obtain ⟨i,hi,hie⟩ := p.mk_mem_edges_iff_exists.mp hem
  have hi4 : i < 4 := by omega
  interval_cases i
  all_goals simp only [Nat.reduceAdd, hp4] at hie
  all_goals rcases Sym2.eq_iff.mp hie with h | h
  all_goals
    obtain ⟨h1,h2⟩ := h
    rw [← h1, ← h2]
    simp [C, RhombusCell.corners]

end Swanepoel
