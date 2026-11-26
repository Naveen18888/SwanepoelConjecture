module
public import Swanepoel.FacialCycleBasisExact
public import Swanepoel.FaceDisplacementCurl
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.exists_family_displacement_potential {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (hc : G.graph.Connected) :
    ∃ P : Fin n → Plane, ∀ e : OrientedEdge G,
      P e.val.2-P e.val.1=retainedDisplacement (G.familyTrackComponents Y) e := by
  let A := G.familyTrackComponents Y
  have hex (i : Fin 2) : ∃ p : Fin n → ℝ, ∀ e : OrientedEdge G,
      p e.val.2-p e.val.1=(retainedDisplacement A e) i := by
    apply G.exists_scalar_potential_of_face_curl_zero hc
      (fun e => (retainedDisplacement A e) i)
    · intro e
      have hr : retainedDisplacement A (reverseEdge e)= -retainedDisplacement A e :=
        trackDisplacement_reverse _ e
      rw [hr]
      rfl
    · intro F
      have hh := congrArg (EuclideanSpace.projₗ i)
        (G.bounded_face_family_displacement_sum ht hY F)
      simp only [map_sum,map_zero] at hh
      change (∑ e∈G.faceIncidentDarts (G.boundedFaceAsPlane F),
        (retainedDisplacement (G.familyTrackComponents Y) e) i)=0 at hh
      exact hh
  choose p hp using hex
  let P (v : Fin n) : Plane := WithLp.toLp 2 (fun i : Fin 2 => p i v)
  refine ⟨P,?_⟩
  intro e
  ext i
  exact hp i e

theorem PennyGraph.family_all_closed_selected_walks_zero {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (hc : G.graph.Connected) (S : Finset (ContactEdge G))
    {a : Fin n} (p : (G.contactGraph S).Walk a a) :
    G.selectedWalkDisplacement (G.familyTrackComponents Y) p=0 := by
  obtain ⟨P,hP⟩ := G.exists_family_displacement_potential ht hY hc
  rw [G.selectedWalkDisplacement_eq_potential _ S P ?_ p,sub_self]
  intro x y h
  exact hP ⟨(x,y),G.contactGraph_le S h⟩

end Swanepoel
