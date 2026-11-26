module
public import Swanepoel.CornerAngleGeometry
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem PennyGraph.corner_terminal_eq_neg_predecessor {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) :
    G.vertexDirection e.val.1 (G.vertexRayRotation e.val.1 ⟨e.val.2,e.property⟩)=
      -carriedVector (G.faceBoundaryPredecessor e) := by
  change G.point (G.vertexRayRotation e.val.1 ⟨e.val.2,e.property⟩).val-G.point e.val.1=
    -(G.point e.val.1-G.point (G.vertexRayRotation e.val.1 ⟨e.val.2,e.property⟩).val)
  abel

theorem PennyGraph.corner_gap_pair_lower {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (e : OrientedEdge G)
    (D : CornerAngleData G e.val.1 ⟨e.val.2,e.property⟩)
    (E : CornerAngleData G (G.faceBoundaryPredecessor e).val.1
      ⟨(G.faceBoundaryPredecessor e).val.2,(G.faceBoundaryPredecessor e).property⟩) :
    3≤D.gap+E.gap := by
  let p := G.faceBoundaryPredecessor e
  let q := G.faceBoundaryPredecessor p
  have hp : p.val.2=e.val.1 := G.faceBoundaryPredecessor_end e
  have hq : q.val.2=p.val.1 := G.faceBoundaryPredecessor_end p
  have hDC : q.val.1≠e.val.2 := by
    intro heq
    have hpAdj := p.property
    have hqAdj := q.property
    rw [hp] at hpAdj
    rw [hq,heq] at hqAdj
    exact ht p.val.1 e.val.1 e.val.2 hpAdj e.property hqAdj
  have hD : unitAngleVector (D.phase-D.gap)= -carriedVector p :=
    D.terminal.trans (G.corner_terminal_eq_neg_predecessor e)
  have hE : unitAngleVector (E.phase-E.gap)= -carriedVector q :=
    E.terminal.trans (G.corner_terminal_eq_neg_predecessor p)
  have hbase : unitAngleVector E.phase=carriedVector p := E.initial
  have hnegative : unitAngleVector (E.phase+3)= -carriedVector p := by
    rw [unitAngleVector_add_three,hbase]
  have hthird : unitAngleVector (E.phase+3+D.gap)=carriedVector e := by
    have h := unitAngleVector_add_eq_of_eq (hD.trans hnegative.symm) D.gap
    rw [sub_add_cancel] at h
    exact h.symm.trans D.initial
  have hdisplacement : unitAngleVector (E.phase-E.gap)-
      (unitAngleVector E.phase+unitAngleVector (E.phase+3+D.gap))=
        G.point q.val.1-G.point e.val.2 := by
    rw [hE,hbase,hthird]
    change -(G.point q.val.2-G.point q.val.1)-
      ((G.point p.val.2-G.point p.val.1)+(G.point e.val.2-G.point e.val.1))= _
    rw [hp,hq]
    abel
  have hfar : 1≤‖unitAngleVector (E.phase-E.gap)-
      (unitAngleVector E.phase+unitAngleVector (E.phase+3+D.gap))‖ := by
    rw [hdisplacement,← dist_eq_norm]
    exact G.separated q.val.1 e.val.2 hDC
  have h := consecutive_corner_gaps_ge_three E.phase E.gap D.gap
    E.gap_gt_one D.gap_gt_one hfar
  linarith only [h]

def PennyGraph.actualCornerAngle {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (e : OrientedEdge G) : CornerAngleData G e.val.1 ⟨e.val.2,e.property⟩ :=
  Classical.choice (G.exists_corner_angle_data ht hdegree e.val.1 ⟨e.val.2,e.property⟩)

theorem PennyGraph.face_corner_gap_sum_lower {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a)
    (F : PlaneFace G) :
    3*((G.faceIncidentDarts F).card : ℝ)≤
      2*∑ e∈G.faceIncidentDarts F,(G.actualCornerAngle ht hdegree e).gap := by
  have hsum := Finset.sum_le_sum (s := G.faceIncidentDarts F) (fun e _ =>
    G.corner_gap_pair_lower ht e (G.actualCornerAngle ht hdegree e)
      (G.actualCornerAngle ht hdegree (G.faceBoundaryPredecessor e)))
  rw [Finset.sum_add_distrib,G.sum_faceBoundaryPredecessor F
    (fun e => (G.actualCornerAngle ht hdegree e).gap)] at hsum
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm,← two_mul] using hsum

end Swanepoel
