module
public import Swanepoel.MeasuredDefectArea
public import Swanepoel.PentagonMixedEstimate
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory

theorem PennyGraph.defect_area_lower_of_face_measure_identity {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hidentity : ∀ F∈G.defectPlaneFaces ht,6≤(G.faceSourcePorts F).card →
      G.faceSignedArea G.point F=volume.real F.val) : G.DefectAreaLowerBound ht := by
  apply G.defect_area_lower_of_large_faces ht hdegree
  intro F hF hports
  rw [hidentity F hF hports]
  exact (G.six_port_face_measure_lower ht hdegree F (G.defectPlaneFace_isBounded ht hF) hports).le

theorem PennyGraph.canonical_quadratic_bound_of_face_measure_identity {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hidentity : ∀ F∈G.defectPlaneFaces ht,6≤(G.faceSourcePorts F).card →
      G.faceSignedArea G.point F=volume.real F.val) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound :=
  G.canonical_quadratic_bound_of_defect_area ht hc hdegree
    (G.defect_area_lower_of_face_measure_identity ht hdegree hidentity)

end Swanepoel
