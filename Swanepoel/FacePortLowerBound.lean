module
public import Swanepoel.FacePortIncidence
public import Swanepoel.SmallContactForests
public import Swanepoel.TrackClassification
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.defect_source_ports_four_le {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    4 ≤ (G.faceSourcePorts F).card := by
  have hf := G.defect_face_retained_by_source_edges ht F hF
  have hedges := hf.four_le_selected_edges ht (G.defectPlaneFace_isBounded ht hF)
  exact hedges.trans (G.facePortEdges_card_le F)

theorem PennyGraph.geometric_effective_nonneg {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    0 ≤ (Fintype.card (TrackComponent G) : ℤ) - 2 * G.faceDefectCount ht :=
  G.effective_nonneg_of_defect_source_ports ht (G.defect_source_ports_four_le ht)

theorem PennyGraph.geometric_terminal_effective_nonneg {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    0 ≤ (G.terminalTrackComponents.card : ℤ) - 2 * G.faceDefectCount ht :=
  G.terminal_effective_nonneg_of_defect_source_ports ht (G.defect_source_ports_four_le ht)

theorem PennyGraph.canonical_componentSystem_K_nonneg {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    0 ≤ (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K := by
  rw [G.componentSystem_K_eq]
  exact G.geometric_terminal_effective_nonneg ht

end Swanepoel
