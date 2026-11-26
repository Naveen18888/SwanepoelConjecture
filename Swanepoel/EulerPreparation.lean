module
public import Swanepoel.OuterFace
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.walk_points_same_drawing_component {n : ℕ} (G : PennyGraph n)
    {a b : Fin n} (p : G.graph.Walk a b) :
    G.point b∈connectedComponentIn G.drawing (G.point a) := by
  induction p with
  | nil => exact mem_connectedComponentIn (G.point_mem_drawing _)
  | @cons a b c hab p ih =>
    have hseg : IsPreconnected (G.edgeTrace a b) :=
      isPreconnected_Icc.image _ (G.continuous_edgePoint a b).continuousOn
    have ha : G.point a∈G.edgeTrace a b :=
      ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
    have hb : G.point b∈G.edgeTrace a b :=
      ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
    have hh := hseg.subset_connectedComponentIn ha (G.edgeTrace_subset_drawing _ _ hab) hb
    rw [connectedComponentIn_eq hh]
    exact ih

theorem PennyGraph.isConnected_drawing {n : ℕ} (G : PennyGraph n)
    (hc : G.graph.Connected) : IsConnected G.drawing := by
  classical
  obtain ⟨a⟩ := hc.nonempty
  have hvertices (b : Fin n) : G.point b∈connectedComponentIn G.drawing (G.point a) := by
    obtain ⟨p⟩ := hc.preconnected a b
    exact G.walk_points_same_drawing_component p
  have hall : G.drawing⊆connectedComponentIn G.drawing (G.point a) := by
    intro z hz
    rcases hz with ⟨b,rfl⟩ | he
    · exact hvertices b
    · obtain ⟨e,⟨t,htt,rfl⟩⟩ := Set.mem_iUnion.mp he
      have hseg : IsPreconnected (G.edgeTrace e.val.1 e.val.2) :=
        isPreconnected_Icc.image _ (G.continuous_edgePoint _ _).continuousOn
      have hb : G.point e.val.1∈G.edgeTrace e.val.1 e.val.2 :=
        ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
      rw [connectedComponentIn_eq (hvertices e.val.1)]
      exact hseg.subset_connectedComponentIn hb (G.edgeTrace_subset_drawing _ _ e.property) ⟨t,htt,rfl⟩
  have heq : G.drawing=connectedComponentIn G.drawing (G.point a) :=
    hall.antisymm (connectedComponentIn_subset _ _)
  exact ⟨⟨G.point a,G.point_mem_drawing a⟩,heq ▸ isPreconnected_connectedComponentIn⟩

theorem PennyGraph.faceEuler_iff_all_faces {n : ℕ} (G : PennyGraph n) :
    G.FaceEuler ↔ (n : ℤ)-G.edgeCount+Nat.card (PlaneFace G)=2 := by
  have h : (Nat.card (PlaneFace G) : ℤ)=(Fintype.card (BoundedFace G) : ℤ)+1 := by
    exact_mod_cast G.all_face_count
  unfold PennyGraph.FaceEuler
  rw [h]
  omega

theorem PennyGraph.euler_with_defects_of_all_faces {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (he : (n : ℤ)-G.edgeCount+Nat.card (PlaneFace G)=2) :
    (n : ℤ)-G.edgeCount+(Fintype.card (RhombusSet G)+G.faceDefectCount ht)=1 :=
  G.euler_with_defects ht (G.faceEuler_iff_all_faces.mpr he)

end Swanepoel
