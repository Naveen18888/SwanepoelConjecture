module
public import Swanepoel.FiveUnitNormalGeometry
public import Swanepoel.PentagonClockwise
public import Swanepoel.DefectHalfOpenCone
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

def dart (i : Fin 5) : OrientedEdge G := ⟨(P.vertex i,P.vertex (i+1)),P.contact i⟩
def normal (i : Fin 5) : Plane := sourceNormal (P.dart i)

theorem normal_norm (i : Fin 5) : ‖P.normal i‖=1 := sourceNormal_norm _

theorem normal_inner (i j : Fin 5) : inner ℝ (P.normal i) (P.normal j)=
    inner ℝ (carriedVector (P.dart i)) (carriedVector (P.dart j)) := by
  simp [normal,sourceNormal,quarterTurn,PiLp.inner_apply,Fin.sum_univ_two]
  ring

theorem normal_clockwise_turn (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) (i : Fin 5) :
    cross2 (P.normal i) (P.normal (i+1))<0 := by
  simp only [normal,← rightNormalMap_carriedVector,rightNormalMap_cross]
  simpa only [dart,carriedVector,add_assoc,show (1:Fin 5)+1=2 by decide] using P.clockwise_turn ht hF i

theorem normal_adjacent_inner_gt_neg_half (ht : G.TriangleFree) (i : Fin 5) :
    (-1/2:ℝ) < inner ℝ (P.normal i) (P.normal (i+1)) := by
  have hne : P.vertex i≠P.vertex (i+2) := by
    intro h
    have hidx := P.vertex_injective h
    have hbad : i≠i+2 := by fin_cases i <;> decide
    exact hbad hidx
  have hcontact : G.graph.Adj (P.vertex (i+1)) (P.vertex (i+2)) := by
    simpa only [add_assoc,show (1:Fin 5)+1=2 by decide] using P.contact (i+1)
  have h := G.two_step_inner_lt_half ht _ _ _ hne (P.contact i) hcontact
  have hneg : G.point (P.vertex i)-G.point (P.vertex (i+1))=
      -(G.point (P.vertex (i+1))-G.point (P.vertex i)) := by abel
  rw [hneg,inner_neg_left] at h
  rw [P.normal_inner]
  change (-1/2:ℝ) < inner ℝ (G.point (P.vertex (i+1))-G.point (P.vertex i))
    (G.point (P.vertex (i+1+1))-G.point (P.vertex (i+1)))
  rw [add_assoc,show (1:Fin 5)+1=2 by decide]
  linarith

theorem normal_sum (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) :
    (∑ i : Fin 5,P.normal i)=0 := by
  have h := G.defect_all_source_normals_sum ht F hF
  rw [← P.darts,Finset.sum_image (by
    intro i _ j _ hij
    exact P.vertex_injective (congrArg (fun e : OrientedEdge G => e.val.1) hij))] at h
  exact h

theorem normal_two_step_inner_le (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht) (i : Fin 5) :
    inner ℝ (P.normal i) (P.normal (i+2))≤ -1/2 := by
  have hrotate : (∑ k : Fin 5,P.normal (i+k))=0 :=
    (Equiv.sum_comp (Equiv.addLeft i) P.normal).trans (P.normal_sum ht hF)
  have hbalance : P.normal i+P.normal (i+2)+P.normal (i+1)=
      -P.normal (i+4)+ -P.normal (i+3) := by
    rw [← neg_add]
    apply eq_neg_iff_add_eq_zero.mpr
    norm_num [Fin.sum_univ_succ] at hrotate
    convert hrotate using 1; abel
  have hidx4 : (i+4)+1=i := by fin_cases i <;> decide
  have hidx1 : (i+1)+1=i+2 := by rw [add_assoc]; rfl
  have hidx2 : (i+2)+1=i+3 := by rw [add_assoc]; rfl
  have h4 := P.normal_adjacent_inner_gt_neg_half ht (i+4)
  rw [hidx4] at h4
  have hc4 := P.normal_clockwise_turn ht hF (i+4)
  rw [hidx4] at hc4
  apply five_unit_chain_two_step_inner_le (P.normal i) (P.normal (i+1)) (P.normal (i+2))
    (-P.normal (i+4)) (-P.normal (i+3))
    (P.normal_norm i) (P.normal_norm (i+1)) (P.normal_norm (i+2))
    (by simp only [norm_neg,P.normal_norm]) (by simp only [norm_neg,P.normal_norm]) hbalance
    (P.normal_adjacent_inner_gt_neg_half ht i)
    (by simpa only [hidx1] using P.normal_adjacent_inner_gt_neg_half ht (i+1))
  · rw [inner_neg_right]
    have hcomm : inner ℝ (P.normal i) (P.normal (i+4))=
        inner ℝ (P.normal (i+4)) (P.normal i) := real_inner_comm _ _
    rw [hcomm]
    linarith
  · rw [inner_neg_right]
    have h := P.normal_adjacent_inner_gt_neg_half ht (i+2)
    rw [hidx2] at h
    linarith
  · exact P.normal_clockwise_turn ht hF i
  · simpa only [hidx1] using P.normal_clockwise_turn ht hF (i+1)
  · have heq : cross2 (P.normal i) (-P.normal (i+4))=cross2 (P.normal (i+4)) (P.normal i) := by
      simp [cross2]
      ring
    rwa [heq]
  · have heq : cross2 (P.normal (i+2)) (-P.normal (i+3))=
        -cross2 (P.normal (i+2)) (P.normal (i+3)) := by simp [cross2]; ring
    rw [heq]
    have h := P.normal_clockwise_turn ht hF (i+2)
    rw [hidx2] at h
    linarith

end PentagonFaceBoundary
end Swanepoel
