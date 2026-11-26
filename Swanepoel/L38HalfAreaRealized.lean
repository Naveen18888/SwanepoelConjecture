module
public import Swanepoel.L38HalfAreaJoinClosure
public import Swanepoel.L38HalfAreaInduction
public import Swanepoel.L38HalfConnectivity
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem half_family_area_comparison (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (side : Bool) (Y : Finset (PlaneFace (B.halfGraph side)))
    (hY : (B.halfGraph side).IsJoinClosed (B.halfGraph_triangleFree ht side) Y) :
    (B.halfGraph side).FamilyAreaComparison (B.halfGraph_triangleFree ht side) Y :=
  (B.halfGraph side).family_area_comparison_of_lower_bound (B.halfGraph_triangleFree ht side)
    (B.halfGraph_connected ht hc side)
    ((B.halfGraph side).retained_area_lower_of_defect_area (B.halfGraph_triangleFree ht side)
      (B.half_defect_area_lower ht hc hcut side hdegree)) hY

theorem exists_half_weighted_area_map (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (side : Bool) :
    let H := B.halfGraph side
    let Y := B.halfRemainderDefects ht side
    let S := B.halfIsolatedDefects ht side
    ∃ P : Fin (B.bankVertices side).card→Plane,
      (∀ e : OrientedEdge H,P e.val.2-P e.val.1=trackDisplacement (H.l38TrackWeight Y S) e) ∧
      Real.sqrt 3/2*((H.familyInternalCrossings (B.halfGraph_triangleFree ht side) Y : ℝ)+Y.card+
        ((H.familyInternalCrossings (B.halfGraph_triangleFree ht side) S : ℝ)+S.card)/4+
          (H.interFamilyCrossings (B.halfGraph_triangleFree ht side) Y S : ℝ)/2)≤
        (∑ F : BoundedFace H,H.faceSignedArea P (H.boundedFaceAsPlane F)) ∧
      ∀ outer : PlaneFace H,¬Bornology.IsBounded outer.val →
        (∑ e∈H.faceIncidentDarts outer,‖P e.val.2-P e.val.1‖)=
          (5/2:ℝ)*(B.isolatedTwoPortPentagons ht side).card+
            2*(G.familyK (B.bankRemainder ht side) : ℝ)-(G.familyPortExcess (B.bankRemainder ht side) : ℝ) := by
  let H := B.halfGraph side
  let Y := B.halfRemainderDefects ht side
  let S := B.halfIsolatedDefects ht side
  have hDis : Disjoint Y S := by
    apply Finset.disjoint_left.mpr
    intro F hFY hFS
    have hRest := B.halfRemainderDefects_eq_sdiff ht hc hcut side
    change F∈B.halfRemainderDefects ht side at hFY
    rw [hRest] at hFY
    exact (Finset.mem_sdiff.mp hFY).2 hFS
  obtain ⟨P,hP,hArea⟩ := H.exists_l38_area_count_lower_of_defect_area (B.halfGraph_triangleFree ht side)
    (B.halfGraph_connected ht hc side) (B.half_defect_area_lower ht hc hcut side hdegree)
    (B.halfRemainderDefects_joinClosed ht hc hcut side) (B.halfIsolatedDefects_joinClosed ht hc hcut side) hDis
  refine ⟨P,hP,hArea,?_⟩
  intro outer houter
  exact B.half_weighted_outer_perimeter_eq ht hc hcut side P hP outer houter

end OrdinaryCutBanks
end Swanepoel
