module
public import Swanepoel.PentagonEdgeSupport
public import Swanepoel.FaceSupport
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.sourceProbe_right_cross {n : ℕ} (G : PennyGraph n) (e : OrientedEdge G) :
    cross2 (carriedVector e) (G.sourceProbe e-G.point e.val.1)<0 := by
  let δ := G.edgeClearance (G.sourceProbeDrawing e) (physicalEdge e) (1/2)
  have hδ : 0<δ := G.sourceProbe_offset_pos e
  have hoff : G.sourceProbe e-G.point e.val.1=
      (1/2:ℝ) • carriedVector e+(-δ) • quarterTurn (carriedVector e) := by
    rw [G.sourceProbe_eq_normal_offset]
    dsimp [PennyGraph.edgePoint,sourceNormal,carriedVector]
    module
  rw [hoff,cross2_add_right,cross2_smul_right,cross2_smul_right,cross2_self,
    cross_quarterTurn,carriedVector_norm]
  nlinarith

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

theorem facePortEdges_endpoints (e : ContactEdge G) (he : e∈G.facePortEdges F) :
    ∃ k l : Fin 5,e.val.1=P.vertex k ∧ e.val.2=P.vertex l := by
  obtain ⟨port,hport,hphysical⟩ := Finset.mem_image.mp he
  rw [← P.darts] at hport
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hport
  have heq : s(e.val.1,e.val.2)=s(P.vertex k,P.vertex (k+1)) := by
    rw [← hphysical,← hk]
    exact physicalEdge_unordered _
  rcases Sym2.eq_iff.mp heq with h | h
  · exact ⟨k,k+1,h.1,h.2⟩
  · exact ⟨k+1,k,h.1,h.2⟩

theorem clockwise_edge_support (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (i j : Fin 5) (hji : j≠i) (hjnext : j≠i+1) :
    cross2 (G.point (P.vertex (i+1))-G.point (P.vertex i))
      (G.point (P.vertex j)-G.point (P.vertex i))<0 := by
  obtain ⟨s,hs,hsides⟩ := P.edge_strict_support ht i
  let e := G.point (P.vertex (i+1))-G.point (P.vertex i)
  let dart : OrientedEdge G := ⟨(P.vertex i,P.vertex (i+1)),P.contact i⟩
  have he : ‖e‖=1 := carriedVector_norm dart
  have hsneg : s<0 := by
    by_contra hn
    have hspos : 0<s := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hs)
    have hpoint (k : Fin 5) : 0≤cross2 e (G.point (P.vertex k)-G.point (P.vertex i)) := by
      by_cases hk : k=i
      · simp [hk,cross2]
      by_cases hk1 : k=i+1
      · simpa only [hk1,e,cross2_self] using (le_refl (0:ℝ))
      have hp := hsides k hk hk1
      exact ((mul_pos_iff.mp hp).resolve_right (fun h => hspos.not_gt h.1)).2.le
    have hlinear (k : Fin 5) :
        (-crossLinear e) (G.point (P.vertex k))≤(-crossLinear e) (G.point (P.vertex i)) := by
      have h := hpoint k
      rw [cross2_sub_right] at h
      change -cross2 e (G.point (P.vertex k))≤ -cross2 e (G.point (P.vertex i))
      linarith
    have hbound := (G.defect_face_retained_by_source_edges ht F hF).linear_support
      (G.defectPlaneFace_isBounded ht hF) (-crossLinear e)
      (neg_ne_zero.mpr (crossLinear_ne_zero e he))
      ((-crossLinear e) (G.point (P.vertex i))) (by
        intro f hf
        obtain ⟨k,l,hk,hl⟩ := P.facePortEdges_endpoints f hf
        rw [hk,hl]
        exact ⟨hlinear k,hlinear l⟩)
    have hface : G.sourceFace dart=F := P.face i
    have hprobe : G.sourceProbe dart∈F.val := by
      rw [← hface]
      exact G.sourceProbe_mem_sourceFace dart
    have hb := hbound _ hprobe
    have hc := G.sourceProbe_right_cross dart
    change cross2 e (G.sourceProbe dart-G.point (P.vertex i))<0 at hc
    rw [cross2_sub_right] at hc
    change -cross2 e (G.sourceProbe dart)≤ -cross2 e (G.point (P.vertex i)) at hb
    linarith
  have h := hsides j hji hjnext
  exact (mul_pos_iff.mp h).resolve_left (fun h => hsneg.not_gt h.1) |>.2

theorem clockwise_turn (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) (i : Fin 5) :
    cross2 (G.point (P.vertex (i+1))-G.point (P.vertex i))
      (G.point (P.vertex (i+2))-G.point (P.vertex (i+1)))<0 := by
  have hi0 : i+2≠i := by fin_cases i <;> decide
  have hi1 : i+2≠i+1 := by fin_cases i <;> decide
  have h := P.clockwise_edge_support ht hF i (i+2) hi0 hi1
  have hdecomp : G.point (P.vertex (i+2))-G.point (P.vertex i)=
      (G.point (P.vertex (i+1))-G.point (P.vertex i))+
        (G.point (P.vertex (i+2))-G.point (P.vertex (i+1))) := by abel
  rw [hdecomp,cross2_add_right,cross2_self,zero_add] at h
  exact h

end PentagonFaceBoundary
end Swanepoel
