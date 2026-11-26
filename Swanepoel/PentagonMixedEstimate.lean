module
public import Swanepoel.PentagonConeCoverRealization
public import Swanepoel.RetainedAreaDecomposition
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.pentagon_crossing_estimate {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a) :
    G.PentagonCrossingEstimate ht := by
  intro Y hY F hFY hfive hports
  have hF := hY.subset_defects hFY
  obtain ⟨P⟩ := G.five_port_face_boundary ht F hF hdegree hfive
  obtain ⟨K⟩ := P.exists_spoke_loops ht hY hFY hports
  have hex (j : Fin 5) := P.sector_covering_axes ht hF hdegree j
  choose axes hnorm hsep hcover using hex
  let axis (code : Fin 5→ℤ) := axes (K.codeSector code)
  apply K.mixed_bound_of_separated_cones ht hY hFY hports hdegree axis
    (fun code b => hnorm (K.codeSector code) b) (fun code => hsep (K.codeSector code))
  intro e he
  have hmem := (Finset.mem_filter.mp he).2
  have heY := (Finset.mem_sdiff.mp hmem.2).1
  have heRoot : G.sourceFace e≠F := by
    intro heq
    exact (Finset.mem_sdiff.mp hmem.2).2 (Finset.mem_singleton.mpr heq)
  have hdata := K.source_crossing_data ht hY hFY hports e (hY.subset_defects heY) heRoot
  exact hcover (K.faceSector (G.sourceFace e)) (sourceNormal e) (sourceNormal_norm e) _
    hdata.1 hdata.2.1 hdata.2.2

theorem PennyGraph.family_quadratic_of_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (harea : ∀ (Y : Finset (PlaneFace G)), G.IsJoinClosed ht Y →
      5*(G.familyBoundaryEndCount Y : ℤ)≤8*G.familyK Y → G.FamilyAreaComparison ht Y)
    (Y : Finset (PlaneFace G)) (hY : G.IsJoinClosed ht Y) :
    10000*G.familyR ht Y≤2379*(G.familyK Y)^2 :=
  G.family_quadratic_of_area_and_pentagons ht hdegree harea (G.pentagon_crossing_estimate ht hdegree) Y hY

theorem PennyGraph.canonical_quadratic_bound_of_defect_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hdefect : G.DefectAreaLowerBound ht) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound :=
  G.canonical_quadratic_bound_of_local_geometry ht hc hdegree hdefect (G.pentagon_crossing_estimate ht hdegree)

theorem PennyGraph.canonical_quadratic_bound_of_large_face_area {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (hlarge : ∀ F∈G.defectPlaneFaces ht,6≤(G.faceSourcePorts F).card →
      Real.sqrt 3/2≤G.faceSignedArea G.point F) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).QuadraticBound :=
  G.canonical_quadratic_bound_of_defect_area ht hc hdegree (G.defect_area_lower_of_large_faces ht hdegree hlarge)

end Swanepoel
