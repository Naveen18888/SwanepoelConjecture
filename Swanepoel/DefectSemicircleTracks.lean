module
public import Swanepoel.DefectTwoSemicirclePorts
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.defect_two_semicircle_terminal_tracks {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (d : Plane) (hd : d≠0) :
    2≤((((G.faceSourcePorts F).filter (fun e => 0 < inner ℝ d (sourceNormal e))).image edgeComponent).card) ∧
      (((G.faceSourcePorts F).filter (fun e => 0 < inner ℝ d (sourceNormal e))).image edgeComponent) ⊆
        G.terminalTrackComponents := by
  let P := (G.faceSourcePorts F).filter (fun e => 0 < inner ℝ d (sourceNormal e))
  have hP : P⊆semicircleSources G d := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have hsource := (Finset.mem_filter.mp he'.1).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsource,he'.2⟩
  constructor
  · rw [selected_semicircle_sources_card_image G ht d P hP]
    exact G.defect_two_semicircle_ports ht F hF hdegree d hd
  · intro c hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact G.defect_source_port_terminal ht hF (Finset.mem_filter.mp he).1

end Swanepoel
