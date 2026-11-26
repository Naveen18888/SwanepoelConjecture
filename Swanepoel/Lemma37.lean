module
public import Swanepoel.FaceMeasureShoelace
public import Swanepoel.QuadraticAreaBridge
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.defect_area_lower {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a) :
    G.DefectAreaLowerBound ht :=
  G.defect_area_lower_of_face_measure_identity ht hdegree
    (fun F hF _ => G.faceSignedArea_eq_measure F (G.defectPlaneFace_isBounded ht hF))

theorem PennyGraph.family_lemma_3_7 {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (Y : Finset (PlaneFace G)) (hY : G.IsJoinClosed ht Y) :
    10000*G.familyR ht Y≤2379*(G.familyK Y)^2 :=
  G.family_quadratic_of_area ht hdegree
    (fun _ hZ _ => G.family_area_comparison_of_lower_bound ht hc
      (G.retained_area_lower_of_defect_area ht (G.defect_area_lower ht hdegree)) hZ) Y hY

theorem PennyGraph.lemma_3_7 {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound :=
  G.canonical_quadratic_bound_of_defect_area ht hc hdegree (G.defect_area_lower ht hdegree)

end Swanepoel
